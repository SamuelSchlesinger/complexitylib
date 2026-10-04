/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Wiring.Defs

/-!
# Input ports in a connected component

A connected closed set containing at least two inputs has no isolated input. Thus its
existing ordinary slot edges suffice for all input ports; no auxiliary port edges are needed.
The underlying multigraph and its degree and size estimates remain unchanged.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Wiring

open scoped Classical
open MultiOutput MultiOutput.Internal WireGraph

variable {σ : Signature} {n s : Nat} {p : Program σ n s} (K : ClosedSet p)

/-- A path from an input to a distinct wire starts with a slot fed by that input. -/
theorem fanout_pos_of_path (j : Fin n) (hj : Wire.input j ∈ K.carrier)
    {w : Wire n s} (hpath : Relation.ReflTransGen (Linked p) (Wire.input j) w)
    (hne : Wire.input j ≠ w) : 0 < fanout K ⟨Wire.input j, hj⟩ := by
  rcases hpath.cases_head with h | ⟨v, hv, -⟩
  · exact False.elim (hne h)
  rcases hv with ⟨g, hbad, -⟩ | ⟨g, rfl, a, ha⟩
  · cases hbad
  · have hg : Wire.gate g ∈ K.carrier := (K.closed g _ ⟨a, ha⟩).mpr hj
    let t : Slot K := ⟨⟨g, a⟩, hg⟩
    have hs : slotSignal K t = ⟨Wire.input j, hj⟩ := Subtype.ext ha
    rw [← hs]
    exact fanout_pos_of_slot K t

/-- Two or more inputs in a connected closed set all have positive fanout. -/
theorem inputsHaveFanout_of_connected
    (hconn : ∀ u ∈ K.carrier, ∀ v ∈ K.carrier, Relation.ReflTransGen (Linked p) u v)
    (hcard : 1 < (SingleCut.inputsIn K.carrier).card) : InputsHaveFanout K := by
  intro j hj
  obtain ⟨k, hk, hkj⟩ := Finset.exists_mem_ne hcard j
  have hk' : Wire.input k ∈ K.carrier := by simpa [SingleCut.inputsIn] using hk
  exact fanout_pos_of_path K j hj (hconn _ hj _ hk') (by
    intro h
    cases h
    exact hkj rfl)

/-- A closed set with a nonisolated input has a nonempty edge type. -/
theorem nonempty_edge_of_inputsHaveFanout (hinput : InputsHaveFanout K)
    (hne : (SingleCut.inputsIn K.carrier).Nonempty) : Nonempty (Edge K) := by
  obtain ⟨j, hj⟩ := hne
  have hj' : Wire.input j ∈ K.carrier := by simpa [SingleCut.inputsIn] using hj
  obtain ⟨e, -⟩ := exists_outgoing K ⟨Wire.input j, hj'⟩ (hinput j hj')
  exact ⟨e⟩

/-- Copy expansion preserves the exact difference between slots and signals. -/
theorem card_edge_sub_card_vertex :
    (Fintype.card (Edge K) : ℝ) - Fintype.card (Vertex K) =
      (Fintype.card (Slot K) : ℝ) - Fintype.card (Signal K) := by
  simp only [Fintype.card_sum]
  push_cast
  ring

/-- An exact slot budget yields an edge-excess bound without charging nullary gates. -/
theorem card_edge_sub_card_vertex_le_of_slot_bound {b : Nat}
    (hslots : Fintype.card (Slot K) ≤ 2 * b) :
    (Fintype.card (Edge K) : ℝ) - Fintype.card (Vertex K) ≤
      2 * (b : ℝ) - (SingleCut.inputsIn K.carrier).card - (gatesIn K.carrier).card := by
  rw [card_edge_sub_card_vertex, card_signal]
  have h : (Fintype.card (Slot K) : ℝ) ≤ 2 * (b : ℝ) := by exact_mod_cast hslots
  push_cast
  linarith

/-- Copy vertices cost at most one vertex per slot. -/
theorem card_vertex_le_of_slot_bound {b : Nat}
    (hslots : Fintype.card (Slot K) ≤ 2 * b) :
    Fintype.card (Vertex K) ≤
      (SingleCut.inputsIn K.carrier).card + (gatesIn K.carrier).card + 2 * b := by
  have hcopy := card_copy_le K
  rw [Fintype.card_sum, card_signal]
  lia

/-- The selected gates that read at least one wire; nullary gates are excluded. -/
noncomputable def activeGates : Finset (Fin s) :=
  (gatesIn K.carrier).filter fun g => 0 < σ.Arity (p.lines g).op

/-- Slots are charged only to gates with nonzero arity. -/
theorem card_slot_le_two_mul_activeGates (hp : p.FanInAtMost 2) :
    Fintype.card (Slot K) ≤ 2 * (activeGates K).card := by
  let φ : Slot K → Fin s × Fin 2 := fun t =>
    (t.1.1, ⟨t.1.2.val, lt_of_lt_of_le t.1.2.isLt (arity_le_of_fanInAtMost p hp t.1.1)⟩)
  have maps : Set.MapsTo φ ↑(Finset.univ : Finset (Slot K))
      ↑(activeGates K ×ˢ (Finset.univ : Finset (Fin 2))) := by
    intro t _
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_univ, and_true, φ]
    simp only [activeGates, gatesIn, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨t.2, lt_of_le_of_lt (Nat.zero_le _) t.1.2.isLt⟩
  have inj : Set.InjOn φ ↑(Finset.univ : Finset (Slot K)) := by
    rintro ⟨⟨g, a⟩, hg⟩ _ ⟨⟨g', a'⟩, hg'⟩ _ heq
    simp only [Prod.mk.injEq, Fin.mk.injEq, φ] at heq
    obtain ⟨rfl, ha⟩ := heq
    have : a = a' := Fin.ext ha
    subst this
    rfl
  have h := Finset.card_le_card_of_injOn φ maps inj
  rw [Finset.card_univ, Finset.card_product, Finset.card_univ, Fintype.card_fin] at h
  lia

/-- Nullary gates do not increase the edge-excess upper bound. -/
theorem card_edge_sub_card_vertex_le_activeGates (hp : p.FanInAtMost 2) :
    (Fintype.card (Edge K) : ℝ) - Fintype.card (Vertex K) ≤
      ((activeGates K).card : ℝ) - (SingleCut.inputsIn K.carrier).card := by
  have h := card_edge_sub_card_vertex_le_of_slot_bound K
    (card_slot_le_two_mul_activeGates K hp)
  have hsub : (activeGates K).card ≤ (gatesIn K.carrier).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hsub' : ((activeGates K).card : ℝ) ≤ (gatesIn K.carrier).card := by exact_mod_cast hsub
  linarith

variable [Nonempty (Edge K)] (hinput : InputsHaveFanout K) (I : Interpretation σ Bool)

/-- The compiler preserves the wire graph exactly. -/
theorem network_toMultigraph : (network K hinput I).toMultigraph = graph K := rfl

/-- The compiled network has no loops. -/
theorem network_loopless : (network K hinput I).Loopless := loopless K

/-- Fan-in at most two gives maximum degree at most three. -/
theorem network_maxDegreeLE_three (hp : p.FanInAtMost 2) :
    (network K hinput I).MaxDegreeLE 3 := maxDegreeLE_three K hp

/-- A connected closed component remains connected after fanout expansion. -/
theorem network_connected (hne : K.carrier.Nonempty)
    (hconn : ∀ u ∈ K.carrier, ∀ v ∈ K.carrier, Relation.ReflTransGen (Linked p) u v) :
    (network K hinput I).Connected := connected K hne hconn

end Algebraic.Cutwidth.Aggregate.Wiring
