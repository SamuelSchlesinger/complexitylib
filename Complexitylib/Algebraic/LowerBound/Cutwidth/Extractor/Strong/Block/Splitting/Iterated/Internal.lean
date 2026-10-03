/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Splitting.Iterated.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Splitting.Iterated.Internal.Hybrid
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Splitting.Iterated.Internal.Prepend
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Splitting.Iterated.Internal.Transport
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Condenser.Repair
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ring

/-!
# Successive splitting of dependent blocks

Repair the first pair while retaining its original joint cap. Correlated
head replacement then preserves the input threshold of every remaining
conditional block. Induction splits those tails, and the two repaired head
coordinates can be prepended at the output threshold. Distance contraction
and conditional averaging charge one local repair error per input block.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem blockSource_split {α : Type*} [Fintype α] (Kin Kout : Nat) (δ : ℝ)
    (repair : ∀ w : α × α → ℝ, IsProbabilityWeight w → CappedWeight w Kin →
      ∃ v : α × α → ℝ, IsProbabilityWeight v ∧ CappedWeight v Kin ∧
        IsBlockSource (fun x : Fin 2 → α => v (x 0, x 1)) Kout ∧
          weightDist w v ≤ δ)
    {t : Nat} {p : (Fin t → α × α) → ℝ} (source : IsBlockSource p Kin) :
    ∃ q : (Fin (2 * t) → α) → ℝ, IsBlockSource q Kout ∧
      weightDist (mapWeight (splitBlockEquiv α t) p) q ≤ (t : ℝ) * δ := by
  classical
  induction t with
  | zero =>
    refine ⟨mapWeight (splitBlockEquiv α 0) p, ?_, ?_⟩
    · exact (isBlockSource_zero_iff _ Kout).mpr
        (source.probability.map (splitBlockEquiv α 0))
    · simp only [weightDist_self, Nat.cast_zero, zero_mul, le_refl]
  | succ t ih =>
    obtain ⟨w, tail, hw, cap, tails, factor⟩ := source.exists_head_tail
    obtain ⟨v, hv, vcap, vsource, headError⟩ := repair w hw cap
    obtain ⟨r, hr, headMarginal, repairDist⟩ :=
      exists_block_tail_replacement t Kin w tail id v hw tails hv vcap
    have repairError : weightDist p r ≤ δ := by
      change weightDist
        (mapWeight (fun az : (α × α) × (Fin t → α × α) => Fin.cons az.1 az.2)
          (fun az => w az.1 * tail az.1 az.2)) r = weightDist (mapWeight id w) v
        at repairDist
      rw [splitBlock_mapWeight_of_factor p w tail factor, mapWeight_id] at repairDist
      exact repairDist.le.trans headError
    obtain ⟨w', tail', hw', cap', tails', factor'⟩ := hr.exists_head_tail
    have sameHead : w' = v :=
      (splitBlock_head_eq r w' tail' (fun a => (tails' a).probability) factor').symm.trans
        headMarginal
    rw [sameHead] at factor'
    choose q hq tailError using fun a => ih (tails' a)
    let Q : (Fin (2 * t + 2) → α) → ℝ :=
      mapWeight (pairPrependEquiv α (2 * t)) (fun az => v az.1 * q az.1 az.2)
    let castTuple : (Fin (2 * t + 2) → α) → (Fin (2 * (t + 1)) → α) :=
      fun x i => x (Fin.cast (Nat.mul_succ 2 t) i)
    have Qsource : IsBlockSource Q Kout := by
      change IsBlockSource
        (mapWeight (fun az : (α × α) × (Fin (2 * t) → α) =>
          (Fin.cons az.1.1 (Fin.cons az.1.2 az.2) : Fin (2 * t + 2) → α))
          (fun az => v az.1 * q az.1 az.2)) Kout
      rw [splitBlock_mapWeight_pairPrepend]
      exact isBlockSource_pairPrepend v q vsource hq
    have hybridError :
        weightDist (mapWeight (splitBlockEquiv α (t + 1)) r)
          (mapWeight castTuple Q) ≤ (t : ℝ) * δ := by
      rw [splitBlock_map_of_factor r v tail' factor']
      exact (weightDist_map_le _ _ castTuple).trans
        (splitBlock_pairPrepend_dist_le_of_le v hv
          (fun a => mapWeight (splitBlockEquiv α t) (tail' a)) q tailError)
    refine ⟨mapWeight castTuple Q, splitBlock_source_cast _ Q Qsource, ?_⟩
    calc
      _ ≤ weightDist (mapWeight (splitBlockEquiv α (t + 1)) p)
            (mapWeight (splitBlockEquiv α (t + 1)) r) +
          weightDist (mapWeight (splitBlockEquiv α (t + 1)) r)
            (mapWeight castTuple Q) := weightDist_triangle _ _ _
      _ ≤ δ + (t : ℝ) * δ := add_le_add
        ((weightDist_map_le p r (splitBlockEquiv α (t + 1))).trans repairError) hybridError
      _ = ((t + 1 : Nat) : ℝ) * δ := by push_cast; ring

end Algebraic.Cutwidth.Extractor.Internal
