/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Joint.SharedMessage.Basic
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Joint.Conjunction.Refined

/-!
# Refined information weights for the actual circuit message

Disjoint original conjunction classes receive their separate graph and
one-eighth costs. All other actual gate bits and the designated output bit
retain the unrestricted Boolean cost.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Joint

open Algebraic.Aggregate.Geometry Entropy
open scoped Classical

/-- Separate conjunction classes extend to a certificate for the actual whole message. -/
noncomputable def outputKeyWeightBoundOfClasses {n g : ℕ} (p : Program signature n g)
    (U : Finset (Fin n)) (out : Wire n g) (T W : Finset (Fin g))
    (disjoint : Disjoint T W)
    (two : ∀ i ∈ T, SelectedPair (p.lines i) U)
    (three : ∀ i ∈ W, 3 ≤ (literalVars (lineLiterals (p.lines i) U)).card) :
    WeightBound (fun x : U → Bool => outputKey p U out (glue U x (fun _ => false)))
      (((g : ℝ) + 1) * Real.log 2 -
        T.card * (Real.binEntropy (1 / 4) - 1 / 2 * Real.log 2) -
        W.card * (Real.log 2 - Real.binEntropy (1 / 8)) +
        U.card * (Real.binEntropy (1 / 4) - 3 / 4 * Real.log 2)) := by
  let R := {i : Fin g // i ∉ T ∪ W}
  have conjunctions := evalLiteralsFamiliesRefinedWeightBound
    (fun i : T => lineLiterals (p.lines i.val) U)
    (fun i : W => lineLiterals (p.lines i.val) U)
    (fun i => (two_le_literalVars_iff_selectedPair _ _).mpr (two i i.property))
    (fun i => three i i.property)
  have other := WeightBound.pi fun i : R => WeightBound.boolean
    (fun x : U → Bool => key p U (glue U x (fun _ => false)) i.val)
  let merge (z : ((T → Bool) × (W → Bool)) × (R → Bool)) (i : Fin g) :=
    if hi : i ∈ T then z.1.1 ⟨i, hi⟩ else
      if hj : i ∈ W then z.1.2 ⟨i, hj⟩ else z.2 ⟨i, by simp [hi, hj]⟩
  have merged := (conjunctions.prod other).map merge
  have gateBound : WeightBound
      (fun x : U → Bool => key p U (glue U x (fun _ => false)))
      ((T.card : ℝ) * Graph.edgeCost + U.card * Graph.vertexCost +
        W.card * Real.binEntropy (1 / 8) + Fintype.card R * Real.log 2) := by
    convert merged using 1
    · funext x i
      dsimp only [merge]
      split
      · exact key_eq_evalLiterals_of_selectedPair p U i (two i (by assumption)) x
      · split
        · apply key_eq_evalLiterals_of_selectedPair p U i _ x
          apply (two_le_literalVars_iff_selectedPair _ _).mp
          exact le_trans (by decide) (three i (by assumption))
        · rfl
    · simp
  let last (x : U → Bool) :=
    if Algebraic.Aggregate.Capacity.selected U out then
      Wire.elim (glue U x (fun _ => false)) (fun _ => false) out else false
  have full := ((WeightBound.boolean last).prod gateBound).map
    (fun (z : Bool × (Fin g → Bool)) (i : Fin (g + 1)) =>
      Fin.lastCases (motive := fun _ => Bool) z.1 z.2 i)
  have remainder : Fintype.card R = g - (T ∪ W).card := by
    have complement := Fintype.card_subtype_compl fun i : Fin g => i ∈ T ∪ W
    simpa only [Fintype.card_fin, Fintype.card_coe] using complement
  have counts : T.card + W.card + Fintype.card R = g := by
    have bound := Finset.card_le_univ (T ∪ W)
    rw [Finset.card_union_of_disjoint disjoint, Fintype.card_fin] at bound
    rw [remainder, Finset.card_union_of_disjoint disjoint]
    lia
  have countsReal : (T.card : ℝ) + W.card + Fintype.card R = g := by exact_mod_cast counts
  convert full using 1
  · rfl
  · dsimp only [Graph.edgeCost, Graph.vertexCost]
    rw [← countsReal]
    ring

end Algebraic.Cutwidth.Aggregate.Geometry.Joint
