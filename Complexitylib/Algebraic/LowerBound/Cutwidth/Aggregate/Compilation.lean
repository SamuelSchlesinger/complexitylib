/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Circuit.Observation
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Circuit.Graph
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Ordering
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Restriction
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Wiring

/-!
# Finite counting for an observed circuit component

A connected closed component with at least two inputs has an exact monoid-network
compiler. Reindexing those inputs and applying a graph ordering gives the finite
acceptance bound, with one multiplicative factor for the aggregate state space.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate

open scoped Classical
open MultiOutput MultiOutput.Internal WireGraph

variable {σ : Signature} {n g m : Nat} {p : Program σ n g}

/-- The predicate obtained by observing every signal of a component, with outside
inputs fixed and its own input coordinates enumerated by `e`. -/
noncomputable def componentFunction (K : ClosedSet p) (I : Interpretation σ Bool)
    {M : Type} [CommMonoid M] (φ : Signal K → Bool → M) (Accept : M → Prop)
    (e : Fin m ≃ ↥(SingleCut.inputsIn K.carrier)) (outside : Fin n → Bool) :
    Cslib.BooleanFunction m :=
  fun x => decide (Accept (∏ w : Signal K,
    φ w (p.trace I (subcubeInput (SingleCut.inputsIn K.carrier) e.symm outside x) w.1)))

/-- A closed connected fan-in-two component has the finite aggregate counting bound.
The ambient gate count bounds selected gates; no assumption on the predicate is used
except rectangle-freeness of the resulting restricted function. -/
theorem card_componentFunction_le (K : ClosedSet p) (I : Interpretation σ Bool)
    {M : Type} [CommMonoid M] [Fintype M]
    (φ : Signal K → Bool → M) (Accept : M → Prop)
    (e : Fin m ≃ ↥(SingleCut.inputsIn K.carrier)) (outside : Fin n → Bool)
    (hp : p.FanInAtMost 2) (hm : 2 ≤ m)
    (hconn : ∀ u ∈ K.carrier, ∀ v ∈ K.carrier, Relation.ReflTransGen (Linked p) u v)
    {A η C : ℝ} (hAη : 0 ≤ A + η) (hC : 0 ≤ C)
    (order : Multigraph.OrderingBound A η C) {Krect : Nat} (hK : 1 < Krect)
    (hrect : RectangleFree (componentFunction K I φ Accept e outside) Krect) :
    ((accepting (componentFunction K I φ Accept e outside)).card : ℝ) ≤
      (((n : ℝ) + 3 * g) * (2 : ℝ) ^ ((A + η) * max ((g : ℝ) - m) 0 +
        3 * Real.logb 2 ((n : ℝ) + 3 * g) + C + 3) + 1) *
        Fintype.card M * Krect ^ 2 := by
  have hmcard : (SingleCut.inputsIn K.carrier).card = m := by
    simpa using (Fintype.card_congr e).symm
  have hinputs : (SingleCut.inputsIn K.carrier).Nonempty :=
    Finset.card_pos.mp (by lia)
  obtain ⟨j, hj⟩ := hinputs
  have hj' : Wire.input j ∈ K.carrier := by simpa [SingleCut.inputsIn] using hj
  have hne : K.carrier.Nonempty := ⟨_, hj'⟩
  have hinput := Wiring.inputsHaveFanout_of_connected K hconn (by lia)
  let : Nonempty (Edge K) := Wiring.nonempty_edge_of_inputsHaveFanout K hinput ⟨j, hj⟩
  let : Nonempty (Vertex K) := ⟨.inl ⟨.input j, hj'⟩⟩
  let N := Wiring.aggregateNetwork K hinput I φ Accept
  let R := N.reindex e
  have hf : R.Computes (componentFunction K I φ Accept e outside) := by
    exact N.reindex_computes e (Wiring.aggregateNetwork_computes K hinput I φ Accept) outside
  have hgate : (gatesIn K.carrier).card ≤ g := by
    simpa using (gatesIn K.carrier).card_le_univ
  have hread : (SingleCut.inputsIn K.carrier).card ≤ n := by
    simpa using (SingleCut.inputsIn K.carrier).card_le_univ
  have hV : (Fintype.card (Vertex K) : ℝ) ≤ (n : ℝ) + 3 * g := by
    have h := card_vertex_le K hp
    have : Fintype.card (Vertex K) ≤ n + 3 * g := by lia
    exact_mod_cast this
  have hdiff : (Fintype.card (Edge K) : ℝ) - Fintype.card (Vertex K) ≤
      (g : ℝ) - m := by
    have h := card_edge_sub_card_vertex_le K hp
    rw [hmcard] at h
    have hg : ((gatesIn K.carrier).card : ℝ) ≤ g := by exact_mod_cast hgate
    linarith
  exact R.card_accepting_le_of_orderingBound hAη hC order hf rfl
    (loopless K) (maxDegreeLE_three K hp) (connected K hne hconn) hV hdiff hK hrect

private theorem card_accepting_le_sum {k : Nat} {ι : Type} [Fintype ι]
    (f : Cslib.BooleanFunction k) (fibre : ι → Cslib.BooleanFunction k)
    (cover : ∀ x, f x = true → ∃ a, fibre a x = true) :
    (accepting f).card ≤ ∑ a, (accepting (fibre a)).card := by
  have hsub : accepting f ⊆ Finset.univ.biUnion (fun a => accepting (fibre a)) := by
    intro x hx
    obtain ⟨a, ha⟩ := cover x (mem_accepting.mp hx)
    exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, mem_accepting.mpr ha⟩
  exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le

section Circuit

open Algebraic.Aggregate

variable {J : Type} {State : J → Type}
  [∀ j, CommMonoid (State j)] [∀ j, Fintype (State j)]

/-- Summing exact guessed computations multiplies the component bound by at most
`2 ^ (budget + 1)`. The one extra bit observes the designated output without an edge. -/
theorem card_restriction_le (p : Program (signature State) n g)
    (out : Wire n g) (a₀ : Guess p) (K : MultiOutput.Internal.ClosedSet (erase p a₀))
    (e : Fin m ≃ ↥(SingleCut.inputsIn K.carrier)) (outside : Fin n → Bool)
    (hm : 2 ≤ m)
    (hconn : ∀ u ∈ K.carrier, ∀ v ∈ K.carrier,
      Relation.ReflTransGen (Linked (erase p a₀)) u v)
    {A η C : ℝ} (hAη : 0 ≤ A + η) (hC : 0 ≤ C)
    (order : Multigraph.OrderingBound A η C) {Krect : Nat} (hK : 1 < Krect)
    (hrect : RectangleFree (fun x => p.trace interpretation x out) Krect) :
    ((accepting (restriction (fun x => p.trace interpretation x out)
      (SingleCut.inputsIn K.carrier) e.symm outside)).card : ℝ) ≤
      (((n : ℝ) + 3 * g) * (2 : ℝ) ^ ((A + η) * max ((g : ℝ) - m) 0 +
        3 * Real.logb 2 ((n : ℝ) + 3 * g) + C + 3) + 1) *
        (2 : ℝ) ^ (budget p + 1) * Krect ^ 2 := by
  let U := SingleCut.inputsIn K.carrier
  let input := subcubeInput U e.symm outside
  let F := restriction (fun x => p.trace interpretation x out) U e.symm outside
  let Ka (a : Guess p) := transportClosedSet p a₀ a K
  let fa (a : Guess p) := componentFunction (Ka a) ordinaryInterpretation
    (fun w value => observe p out w.1 value) (ComponentAccept p a K.carrier out outside)
    e outside
  have hsem (a : Guess p) (x : Fin m → Bool) :
      fa a x = true ↔ AcceptsGuess p a out (input x) := by
    change decide (ComponentAccept p a K.carrier out outside
      (∏ w : Signal (Ka a), observe p out w.1
        ((erase p a).trace ordinaryInterpretation (input x) w.1))) = true ↔ _
    rw [decide_eq_true_iff]
    exact componentAccept_iff p a (Ka a) out outside (input x) (by
      intro j hj
      simp only [input, subcubeInput, Ka, transportClosedSet] at *
      simp [U, hj])
  have hsub (a : Guess p) : ∀ x, fa a x = true → F x = true := by
    intro x hx
    exact ((acceptsGuess_iff p a out (input x)).mp ((hsem a x).mp hx)).2
  have hfree : RectangleFree F Krect := hrect.restriction U e.symm outside
  have hfreea (a : Guess p) : RectangleFree (fa a) Krect := by
    intro S P Q hPQ
    exact hfree S P Q (fun x hx y hy => hsub a _ (hPQ x hx y hy))
  let B : ℝ := ((n : ℝ) + 3 * g) * (2 : ℝ) ^
    ((A + η) * max ((g : ℝ) - m) 0 +
      3 * Real.logb 2 ((n : ℝ) + 3 * g) + C + 3) + 1
  have hbound (a : Guess p) :
      ((accepting (fa a)).card : ℝ) ≤ B * Fintype.card (Observation p) * Krect ^ 2 :=
    card_componentFunction_le (Ka a) ordinaryInterpretation
      (fun w value => observe p out w.1 value) (ComponentAccept p a K.carrier out outside)
      e outside (erase_fanInAtMost p a) hm
      (connected_transportClosedSet p a₀ a K hconn) hAη hC order hK (hfreea a)
  have hcover : (accepting F).card ≤ ∑ a, (accepting (fa a)).card := by
    apply card_accepting_le_sum F fa
    intro x hx
    refine ⟨actualGuess p (input x), (hsem _ x).mpr ?_⟩
    exact (acceptsGuess_iff p _ out (input x)).mpr ⟨rfl, hx⟩
  have hstates : (Fintype.card (Guess p) : ℝ) * Fintype.card (Observation p) ≤
      (2 : ℝ) ^ (budget p + 1) := by
    exact_mod_cast card_guess_mul_card_observation_le p
  have hB : 0 ≤ B := by dsimp [B]; positivity
  calc ((accepting F).card : ℝ)
      ≤ ∑ a, ((accepting (fa a)).card : ℝ) := by exact_mod_cast hcover
    _ ≤ ∑ _a : Guess p, B * Fintype.card (Observation p) * Krect ^ 2 :=
      Finset.sum_le_sum fun a _ => hbound a
    _ = B * ((Fintype.card (Guess p) : ℝ) * Fintype.card (Observation p)) *
        Krect ^ 2 := by simp [Finset.sum_const]; ring
    _ ≤ B * (2 : ℝ) ^ (budget p + 1) * Krect ^ 2 := by
      gcongr

end Circuit

end Algebraic.Cutwidth.Aggregate
