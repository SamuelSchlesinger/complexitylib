/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Message
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Message.Bias
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Joint.Conjunction.Basic
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Joint.Conjunction.Family
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Graph.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Graph.Internal.Weights

/-!
# Actual circuit messages as finite signed literal sets

Selected conjunction slots become literal sets on Alice's input coordinates.
Identical slots collapse and conflicting literals remain, preserving the original
message exactly without a circuit normalization assumption.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Joint

open Algebraic.Aggregate.Geometry
open scoped Classical

/-- Signed literals on selected primary inputs of an actual conjunction line. -/
noncomputable def conjunctionLiterals {r n g : ℕ} (polarity : Fin r → Bool)
    (wires : Fin r → Wire n g) (U : Finset (Fin n)) : Finset (U × Bool) :=
  Finset.univ.filter fun t => ∃ slot, wires slot = .input t.1.val ∧ polarity slot = t.2

/-- Literal representation of a conjunction message; affine lines have no literals. -/
noncomputable def lineLiterals {n g : ℕ} (line : Line signature n g)
    (U : Finset (Fin n)) : Finset (U × Bool) :=
  match line with
  | ⟨.affine .., _⟩ => ∅
  | ⟨.conjunction _ polarity _, wires⟩ => conjunctionLiterals polarity wires U

/-- Membership records an actual selected primary slot and its polarity. -/
theorem mem_conjunctionLiterals {r n g : ℕ} (polarity : Fin r → Bool)
    (wires : Fin r → Wire n g) (U : Finset (Fin n)) (t : U × Bool) :
    t ∈ conjunctionLiterals polarity wires U ↔
      ∃ slot, wires slot = .input t.1.val ∧ polarity slot = t.2 := by
  simp only [conjunctionLiterals, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The variables of a selected literal set are exactly selected primary wires. -/
theorem mem_conjunctionLiteralVars {r n g : ℕ} (polarity : Fin r → Bool)
    (wires : Fin r → Wire n g) (U : Finset (Fin n)) (i : U) :
    i ∈ literalVars (conjunctionLiterals polarity wires U) ↔
      ∃ slot, wires slot = .input i.val := by
  rw [mem_literalVars]
  simp only [mem_conjunctionLiterals]
  constructor
  · rintro ⟨b, slot, wire, _⟩
    exact ⟨slot, wire⟩
  · rintro ⟨slot, wire⟩
    exact ⟨polarity slot, slot, wire, rfl⟩

/-- Literal-set evaluation is exactly the original partial conjunction message. -/
theorem eval_conjunctionLiterals {r n g : ℕ} (polarity : Fin r → Bool)
    (wires : Fin r → Wire n g) (U : Finset (Fin n)) (x : U → Bool) :
    evalLiterals (conjunctionLiterals polarity wires U) x =
      conjunctionSummary polarity wires U
        (Wire.elim (glue U x (fun _ => false)) (fun _ => false)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [evalLiterals, conjunctionSummary, decide_eq_true_eq]
  constructor
  · intro holds slot selected
    cases eq : wires slot with
    | gate gate => simp [eq, Algebraic.Aggregate.Capacity.selected] at selected
    | input i =>
      have mem : i ∈ U := by simpa [eq, Algebraic.Aggregate.Capacity.selected] using selected
      have lit := holds (⟨i, mem⟩, polarity slot)
        ((mem_conjunctionLiterals _ _ _ _).mpr ⟨slot, eq, rfl⟩)
      simpa [eq, glue, mem] using lit
  · intro holds t ht
    obtain ⟨slot, wire, polarity_eq⟩ := (mem_conjunctionLiterals _ _ _ _).mp ht
    have selected : Algebraic.Aggregate.Capacity.selected U (wires slot) := by
      simp [wire, Algebraic.Aggregate.Capacity.selected, t.1.property]
    have lit := holds slot selected
    simpa [wire, glue, t.1.property, polarity_eq] using lit

/-- Conjunction lines retain exactly their literal-set message. -/
theorem lineSummary_eq_evalLiterals {n g : ℕ} (line : Line signature n g)
    (conjunction : line.op.isConjunction = true) (U : Finset (Fin n)) (x : U → Bool) :
    lineSummary line U (Wire.elim (glue U x (fun _ => false)) (fun _ => false)) =
      evalLiterals (lineLiterals line U) x := by
  rcases line with ⟨op, wires⟩
  cases op with
  | affine r bias coefficient => simp [Op.isConjunction] at conjunction
  | conjunction r polarity negated => exact (eval_conjunctionLiterals polarity wires U x).symm

/-- A selected pair is exactly a literal-set message on at least two variables. -/
theorem two_le_literalVars_iff_selectedPair {n g : ℕ} (line : Line signature n g)
    (U : Finset (Fin n)) :
    2 ≤ (literalVars (lineLiterals line U)).card ↔ SelectedPair line U := by
  rcases line with ⟨op, wires⟩
  cases op with
  | affine r bias coefficient => simp [lineLiterals, literalVars, SelectedPair, Op.isConjunction]
  | conjunction r polarity negated =>
    change 1 < (literalVars (conjunctionLiterals polarity wires U)).card ↔ _
    rw [Finset.one_lt_card]
    simp only [mem_conjunctionLiteralVars]
    constructor
    · rintro ⟨i, ⟨s, hs⟩, j, ⟨t, ht⟩, different⟩
      refine ⟨rfl, i.val, ?_, j.val, ?_, ?_, i.property, j.property⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨s, hs⟩⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨t, ht⟩⟩
      · exact fun same => different (Subtype.ext same)
    · rintro ⟨_, i, hi, j, hj, different, hiU, hjU⟩
      refine ⟨⟨i, hiU⟩, (Finset.mem_filter.mp hi).2,
        ⟨j, hjU⟩, (Finset.mem_filter.mp hj).2, ?_⟩
      exact fun same => different (congrArg Subtype.val same)

/-- The gate coordinates of the actual message agree with the selected literal sets. -/
theorem key_eq_evalLiterals_of_selectedPair {n g : ℕ} (p : Program signature n g)
    (U : Finset (Fin n)) (gate : Fin g) (selected : SelectedPair (p.lines gate) U)
    (x : U → Bool) :
    key p U (glue U x (fun _ => false)) gate = evalLiterals (lineLiterals (p.lines gate) U) x :=
  lineSummary_eq_evalLiterals (p.lines gate) selected.1 U x

/-- A joint certificate on the eligible conjunctions extends to the actual whole message. -/
noncomputable def outputKeyWeightBoundOfLiterals {n g : ℕ} (p : Program signature n g)
    (U : Finset (Fin n)) (out : Wire n g)
    (literalBound : Entropy.WeightBound
      (fun (x : U → Bool) (i : {gate : Fin g // SelectedPair (p.lines gate) U}) =>
        evalLiterals (lineLiterals (p.lines i.val) U) x)
      (Fintype.card {gate : Fin g // SelectedPair (p.lines gate) U} * Entropy.Graph.edgeCost +
        U.card * Entropy.Graph.vertexCost)) :
    Entropy.WeightBound (fun x : U → Bool => outputKey p U out (glue U x (fun _ => false)))
      (((g : ℝ) + 1) * Real.log 2 -
        (Finset.univ.filter fun gate : Fin g => SelectedPair (p.lines gate) U).card *
          (Real.binEntropy (1 / 4) - 1 / 2 * Real.log 2) +
        U.card * (Real.binEntropy (1 / 4) - 3 / 4 * Real.log 2)) := by
  let P (i : Fin g) := SelectedPair (p.lines i) U
  let J := {i : Fin g // P i}
  let R := {i : Fin g // ¬ P i}
  let other (x : U → Bool) (i : R) := key p U (glue U x (fun _ => false)) i.val
  have otherBound := Entropy.WeightBound.pi (fun i : R =>
    Entropy.WeightBound.boolean (fun x : U → Bool => other x i))
  let merge (z : (J → Bool) × (R → Bool)) (i : Fin g) :=
    if h : P i then z.1 ⟨i, h⟩ else z.2 ⟨i, h⟩
  have merged := (literalBound.prod otherBound).map merge
  have gateBound : Entropy.WeightBound
      (fun x : U → Bool => key p U (glue U x (fun _ => false)))
      ((Fintype.card J : ℝ) * Entropy.Graph.edgeCost + U.card * Entropy.Graph.vertexCost +
        Fintype.card R * Real.log 2) := by
    convert merged using 1
    · funext x i
      dsimp only [merge]
      split
      · exact key_eq_evalLiterals_of_selectedPair p U i (by assumption) x
      · rfl
    · simp [J, P]
  let last (x : U → Bool) :=
    if Algebraic.Aggregate.Capacity.selected U out then
      Wire.elim (glue U x (fun _ => false)) (fun _ => false) out else false
  have full := ((Entropy.WeightBound.boolean last).prod gateBound).map
    (fun (z : Bool × (Fin g → Bool)) (i : Fin (g + 1)) =>
      Fin.lastCases (motive := fun _ => Bool) z.1 z.2 i)
  have counts : Fintype.card J + Fintype.card R = g := by
    simp only [J, R, Fintype.card_subtype]
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin g))) P
  have countsReal : (Fintype.card J : ℝ) + Fintype.card R = g := by exact_mod_cast counts
  have selectedCount : Fintype.card J =
      (Finset.univ.filter fun gate : Fin g => SelectedPair (p.lines gate) U).card :=
    Fintype.card_subtype _
  convert full using 1
  · rfl
  · rw [← selectedCount]
    dsimp only [Entropy.Graph.edgeCost, Entropy.Graph.vertexCost]
    rw [← countsReal]
    ring

/-- The actual one-way circuit message obeys the joint conjunction information bound. -/
noncomputable def outputKeyWeightBound {n g : ℕ} (p : Program signature n g)
    (U : Finset (Fin n)) (out : Wire n g) :
    Entropy.WeightBound (fun x : U → Bool => outputKey p U out (glue U x (fun _ => false)))
      (((g : ℝ) + 1) * Real.log 2 -
        (Finset.univ.filter fun gate : Fin g => SelectedPair (p.lines gate) U).card *
          (Real.binEntropy (1 / 4) - 1 / 2 * Real.log 2) +
        U.card * (Real.binEntropy (1 / 4) - 3 / 4 * Real.log 2)) := by
  apply outputKeyWeightBoundOfLiterals p U out
  have bound := evalLiteralsFamilyWeightBound
    (fun i : {gate : Fin g // SelectedPair (p.lines gate) U} => lineLiterals (p.lines i.val) U)
    (fun i => (two_le_literalVars_iff_selectedPair _ _).mpr i.property)
  simpa only [Fintype.card_coe] using bound

end Algebraic.Cutwidth.Aggregate.Geometry.Joint
