/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Wiring

/-!
# Signals and generators of a cut

The cut-counting lemma `Network.card_accepting_le_of_realized` charges a prefix
cut by the number of bit patterns that satisfying assignments realize on it,
not by its number of edges. In the wiring network of a binary circuit every
edge carrying one signal carries the same bit (`eq_firstOut_of_satisfies`),
and a gate whose two argument signals are both carried by a set of edges `C`
carries a function of their bits. The patterns realized on `C` are therefore
determined by one edge per *generator*: a signal carried by `C` that is not a
reachable gate both of whose argument signals are carried by `C`.

The main results are

* `determines_of_generators`: a subset of `C` containing an edge of every
  generator determines `C`;
* `card_realized_le_two_pow_generators`: at most `2 ^ |generators C|` patterns
  are realized on `C`, hence at most `2 ^ |signals C|`;
* `card_accepting_le_of_generators`: the cut-counting lemma for circuits, with
  every prefix cut charged by its generators instead of its edges.

A layout theorem bounding the generators of every prefix cut of some vertex
ordering is the target statement for signal (hypergraph) layouts; none is
proved here, and `FourN` continues to charge edges.
-/

@[expose] public section

namespace Algebraic
namespace Cutwidth
namespace Wiring

open scoped Classical

variable {n s : Nat} (p : Program Binary.signature n s) (out : Fin s)

/-- The signals carried by a set of edges. -/
noncomputable def signals (C : Finset (Edge p out)) : Finset (Signal p out) :=
  C.image (signal p out)

theorem mem_signals {C : Finset (Edge p out)} {w : Signal p out} :
    w ∈ signals p out C ↔ ∃ e ∈ C, signal p out e = w := by
  simp [signals]

theorem card_signals_le (C : Finset (Edge p out)) : (signals p out C).card ≤ C.card :=
  Finset.card_image_le

/-- A signal is determined within `C` when it is a reachable gate both of whose
argument signals are carried by `C`. -/
def DeterminedIn (C : Finset (Edge p out)) (w : Signal p out) : Prop :=
  ∃ (g : Fin s) (h : Reach p out (Wire.gate g)), w = ⟨Wire.gate g, h⟩ ∧
    ∀ a : Fin 2, slotSignal p out ⟨(g, a), h⟩ ∈ signals p out C

/-- The generators of `C`: the signals carried by `C` that are not determined
within `C`. -/
noncomputable def generators (C : Finset (Edge p out)) : Finset (Signal p out) :=
  (signals p out C).filter fun w => ¬ DeterminedIn p out C w

theorem mem_generators {C : Finset (Edge p out)} {w : Signal p out} :
    w ∈ generators p out C ↔ w ∈ signals p out C ∧ ¬ DeterminedIn p out C w := by
  simp [generators]

theorem generators_subset (C : Finset (Edge p out)) :
    generators p out C ⊆ signals p out C :=
  Finset.filter_subset _ _

theorem card_generators_le (C : Finset (Edge p out)) : (generators p out C).card ≤ C.card :=
  (Finset.card_le_card (generators_subset p out C)).trans (card_signals_le p out C)

/-- Every edge carries a signal with positive fan-out. -/
theorem fanout_signal_pos (e : Edge p out) : 0 < fanout p out (signal p out e) := by
  rcases e with t | ⟨w, k⟩
  · exact fanout_pos_of_slot p out t
  · have := k.isLt
    show 0 < fanout p out w
    omega

/-- Two satisfying assignments that agree on an edge of every generator of `C`
agree on all of `C`: along the program order, a determined gate carries its
operation applied to bits that already agree. -/
theorem determines_of_generators {C T : Finset (Edge p out)}
    (hgen : ∀ w ∈ generators p out C, ∃ e ∈ T, signal p out e = w) :
    (network p out).Determines C T := by
  intro x α hα y β hβ agree
  suffices key : ∀ m, ∀ w : Signal p out, w.1.index.val = m → w ∈ signals p out C →
      α (firstOut p out w) = β (firstOut p out w) by
    intro e he
    rw [eq_firstOut_of_satisfies p out hα (signal p out e) e rfl,
      eq_firstOut_of_satisfies p out hβ (signal p out e) e rfl]
    exact key _ _ rfl ((mem_signals p out).mpr ⟨e, he, rfl⟩)
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro w hm hw
  by_cases hdet : DeterminedIn p out C w
  · obtain ⟨g, h, rfl, hslots⟩ := hdet
    obtain ⟨e, he, hsig⟩ := (mem_signals p out).mp hw
    have hpos : 0 < fanout p out ⟨Wire.gate g, h⟩ := by
      rw [← hsig]
      exact fanout_signal_pos p out e
    rw [(hα.1 (.inl ⟨Wire.gate g, h⟩) g h rfl).1 hpos,
      (hβ.1 (.inl ⟨Wire.gate g, h⟩) g h rfl).1 hpos]
    unfold opValue
    have slot (a : Fin 2) : α (.inl ⟨(g, a), h⟩) = β (.inl ⟨(g, a), h⟩) := by
      rw [eq_firstOut_of_satisfies p out hα (slotSignal p out ⟨(g, a), h⟩) _ rfl,
        eq_firstOut_of_satisfies p out hβ (slotSignal p out ⟨(g, a), h⟩) _ rfl]
      refine ih _ ?_ _ rfl (hslots a)
      rw [← hm]
      exact lines_wires_lt p g a
    rw [slot 0, slot 1]
  · obtain ⟨e, he, hsig⟩ := hgen w ((mem_generators p out).mpr ⟨hw, hdet⟩)
    rw [← eq_firstOut_of_satisfies p out hα w e hsig,
      ← eq_firstOut_of_satisfies p out hβ w e hsig]
    exact agree e he

/-- One edge of `C` per generator is a determining subset with exactly as many
edges as generators. -/
theorem exists_determining (C : Finset (Edge p out)) :
    ∃ T ⊆ C, T.card = (generators p out C).card ∧ (network p out).Determines C T := by
  have choice : ∀ w ∈ generators p out C, ∃ e ∈ C, signal p out e = w :=
    fun w hw => (mem_signals p out).mp (generators_subset p out C hw)
  have : Nonempty (Edge p out) := ⟨.inl ⟨(out, 0), Reach.out⟩⟩
  choose! rep hrep using choice
  have image_subset : (generators p out C).image rep ⊆ C := by
    intro e he
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp he
    exact (hrep w hw).1
  refine ⟨(generators p out C).image rep, image_subset, ?_, ?_⟩
  · apply Finset.card_image_of_injOn
    intro w hw w' hw' heq
    rw [← (hrep w hw).2, ← (hrep w' hw').2, heq]
  · exact determines_of_generators p out fun w hw =>
      ⟨rep w, Finset.mem_image_of_mem rep hw, (hrep w hw).2⟩

/-- The patterns realized on `C` are bounded by its generators. -/
theorem card_realized_le_two_pow_generators (C : Finset (Edge p out)) :
    ((network p out).realized C).card ≤ 2 ^ (generators p out C).card := by
  obtain ⟨T, hT, hcard, hdet⟩ := exists_determining p out C
  rw [← hcard]
  exact (network p out).card_realized_le_of_determines hT hdet

/-- The patterns realized on `C` are bounded by its signals. -/
theorem card_realized_le_two_pow_signals (C : Finset (Edge p out)) :
    ((network p out).realized C).card ≤ 2 ^ (signals p out C).card :=
  (card_realized_le_two_pow_generators p out C).trans
    (Nat.pow_le_pow_right two_pos (Finset.card_le_card (generators_subset p out C)))

/-- **The cut-counting lemma for circuits, charged by generators.** For a vertex
ordering of the wiring network in which the cut before every vertex, together
with that vertex's edges, has at most `w` generators, a circuit computing a
`K`-rectangle-free function either accepts fewer than `K · 2 ^ (n - n')`
inputs, where `n'` inputs are read, or accepts at most
`|V| · 2 ^ w · (K - 1) ^ 2` inputs. -/
theorem card_accepting_le_of_generators [LinearOrder (Vertex p out)] {w : Nat}
    (hw : ∀ v, (generators p out ((network p out).charged v)).card ≤ w)
    {K : Nat} (hK : 1 < K)
    (hrect : RectangleFree (fun x => p.eval Binary.interpretation x out) K) :
    (accepting fun x => p.eval Binary.interpretation x out).card <
        K * 2 ^ (n - (read p out).card) ∨
      (accepting fun x => p.eval Binary.interpretation x out).card ≤
        Fintype.card (Vertex p out) * 2 ^ w * (K - 1) ^ 2 := by
  have h := (network p out).card_accepting_le_of_realized (network_computes p out)
    (P := 2 ^ w) (fun v => (card_realized_le_two_pow_generators p out _).trans
      (Nat.pow_le_pow_right two_pos (hw v))) hK hrect
  exact h

end Wiring

end Cutwidth
end Algebraic
