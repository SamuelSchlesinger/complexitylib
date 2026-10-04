/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Joint.Conjunction.Bias
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Graph
import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Graph.Internal.Weights
import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Graph.Internal.Constants

/-!
# Joint weights for arbitrary signed conjunction families

Consistent two-variable conjunctions use the graph certificate. Conjunctions on
three or more variables have enough marginal bias to pay the same edge cost, and
inconsistent conjunctions are constant. Their weights combine without an assumption
that the actual messages are independent.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Joint

open Entropy
open scoped BigOperators Classical

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

/-- Any family of conjunctions on at least two distinct primary variables obeys
the joint graph cost, including arbitrary repetitions and contradictory literals. -/
noncomputable def evalLiteralsFamilyWeightBound (L : I → Finset (V × Bool))
    (two : ∀ i, 2 ≤ (literalVars (L i)).card) :
    WeightBound (fun x i => evalLiterals (L i) x)
      (Fintype.card I * Graph.edgeCost + Fintype.card V * Graph.vertexCost) := by
  let P (i : I) : Prop := ConsistentLiterals (L i) ∧ (literalVars (L i)).card = 2
  let G := {i : I // P i}
  let R := {i : I // ¬ P i}
  have represent (i : G) : ∃ e : SignedEdge V, e.eval = evalLiterals (L i) :=
    exists_signedEdge_of_card_eq_two i.property.1 i.property.2
  let edge (i : G) := Classical.choose (represent i)
  have evaluated (i : G) : (edge i).eval = evalLiterals (L i) :=
    Classical.choose_spec (represent i)
  have graph : WeightBound (fun x (i : G) => evalLiterals (L i) x)
      (Fintype.card G * Graph.edgeCost + Fintype.card V * Graph.vertexCost) := by
    have bound := Graph.weightBound edge
    simpa only [evaluated] using bound
  have other (i : R) : WeightBound (evalLiterals (L i)) Graph.edgeCost := by
    by_cases consistent : ConsistentLiterals (L i)
    · have large : 3 ≤ (literalVars (L i)).card := by
        have lower := two i
        have not_two : (literalVars (L i)).card ≠ 2 :=
          fun equal => i.property ⟨consistent, equal⟩
        lia
      exact evalLiteralsWeightBoundOfThreeLe large
    · rw [evalLiterals_eq_false_of_not_consistent consistent]
      exact (WeightBound.const false).mono Graph.edgeCost_nonneg
  have rest : WeightBound (fun x (i : R) => evalLiterals (L i) x)
      (Fintype.card R * Graph.edgeCost) := by
    simpa using WeightBound.pi other
  let readout (message : (G → Bool) × (R → Bool)) (i : I) : Bool :=
    if h : P i then message.1 ⟨i, h⟩ else message.2 ⟨i, h⟩
  have decoded : (fun x => readout
      ((fun i : G => evalLiterals (L i) x), fun i : R => evalLiterals (L i) x)) =
      (fun x i => evalLiterals (L i) x) := by
    funext x i
    dsimp [readout]
    split_ifs <;> rfl
  have result := (graph.prod rest).map readout
  rw [decoded] at result
  apply result.mono
  have cards : Fintype.card G + Fintype.card R = Fintype.card I := by
    have complement := Fintype.card_subtype_compl P
    have subset := Fintype.card_subtype_le P
    change Fintype.card R = Fintype.card I - Fintype.card G at complement
    change Fintype.card G ≤ Fintype.card I at subset
    lia
  have cards_real : (Fintype.card G : ℝ) + Fintype.card R = Fintype.card I := by
    exact_mod_cast cards
  apply le_of_eq
  calc
    _ = ((Fintype.card G : ℝ) + Fintype.card R) * Graph.edgeCost +
        Fintype.card V * Graph.vertexCost := by ring
    _ = _ := by rw [cards_real]

end Algebraic.Cutwidth.Aggregate.Geometry.Joint
