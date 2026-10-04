/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Multigraph
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum

/-!
# The wire graph of a closed set of wires

Fix a program over any signature whose gates have at most two arguments, and a *closed* set
`K` of wires: a gate lies in `K` exactly when the wires it reads do. The wire graph of `K` has a
vertex for every wire of `K` and, for a wire read by `f ≥ 2` argument slots, `f - 1` copy
vertices of degree three through which the signal is routed. Its edges are the argument slots
of the gates of `K` and the incoming edge of every copy vertex. This is the construction of
`Cutwidth.Wiring`, freed from the binary basis and from the reachability restriction.

The main results are

* `loopless`, `maxDegreeLE_three`, `connected`: the hypotheses of the graph-ordering bound,
  the last one when `K` is nonempty and connected in the wire graph;
* `card_forward_add_card_backward_le`: for every set `L` of vertices, the forward and backward
  signals of the wires whose vertices lie in `L` number at most the edges of the cut of `L`.
  Every edge carries one signal, and the edges carrying a signal form a tree joining its wire
  to every gate reading it, so a signal crossing the split crosses the cut;
* `card_edge_sub_card_vertex_le`, `card_vertex_le`: the excess of edges over vertices is at most
  the number of gates minus the number of inputs in `K`, and there are at most `i + 3 g`
  vertices for `i` inputs and `g` gates in `K`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput.Internal

open scoped Classical
open SingleCut

variable {σ : Signature} {n s : Nat}

/-- A gate of a program with fan-in at most `r` has at most `r` arguments. -/
theorem arity_le_of_fanInAtMost {r : Nat} :
    ∀ {s : Nat} (p : Program σ n s), p.FanInAtMost r → ∀ g, σ.Arity (p.lines g).op ≤ r
  | 0, .empty, _, g => g.elim0
  | _, .gate p line, h, g => by
    obtain ⟨hp, hl⟩ := h
    induction g using Fin.lastCases with
    | last =>
      rw [Program.lines_gate_last]
      exact hl
    | cast g =>
      rw [Program.lines_gate_castSucc]
      exact arity_le_of_fanInAtMost p hp g

/-- A closed set of wires: a gate lies in the set exactly when every wire it reads does. -/
structure ClosedSet (p : Program σ n s) where
  /-- The wires of the set. -/
  carrier : Finset (Wire n s)
  /-- A gate and each wire it reads lie on the same side. -/
  closed : ∀ g w, p.Reads g w → (Wire.gate g ∈ carrier ↔ w ∈ carrier)

namespace WireGraph

variable {p : Program σ n s} (K : ClosedSet p)

/-- The wires of `K`: the signals of the wire graph. -/
abbrev Signal := {w : Wire n s // w ∈ K.carrier}

/-- The argument slots of the gates of `K`. -/
abbrev Slot := {t : (Σ g : Fin s, Fin (σ.Arity (p.lines g).op)) // Wire.gate t.1 ∈ K.carrier}

/-- The wire read by a slot. -/
def slotWire (t : Slot K) : Wire n s :=
  (p.lines t.1.1).wires t.1.2

theorem reads_slotWire (t : Slot K) : p.Reads t.1.1 (slotWire K t) :=
  ⟨t.1.2, rfl⟩

/-- The signal read by a slot. -/
def slotSignal (t : Slot K) : Signal K :=
  ⟨slotWire K t, (K.closed _ _ (reads_slotWire K t)).mp t.2⟩

/-- The gate owning a slot. -/
def slotGate (t : Slot K) : Signal K :=
  ⟨Wire.gate t.1.1, t.2⟩

/-- The slots fed by a signal. -/
noncomputable def slots (w : Signal K) : Finset (Slot K) :=
  Finset.univ.filter fun t => slotSignal K t = w

theorem mem_slots {w : Signal K} {t : Slot K} : t ∈ slots K w ↔ slotSignal K t = w := by
  simp [slots]

/-- The number of slots fed by a signal. -/
noncomputable def fanout (w : Signal K) : Nat :=
  (slots K w).card

theorem fanout_pos_of_slot (t : Slot K) : 0 < fanout K (slotSignal K t) :=
  Finset.card_pos.mpr ⟨t, (mem_slots K).mpr rfl⟩

/-- A signal feeding `f ≥ 2` slots is routed through `f - 1` copy vertices. -/
abbrev Copy := Σ w : Signal K, Fin (fanout K w - 1)

/-- Vertices: the wires of `K` and the copy vertices. -/
abbrev Vertex := Signal K ⊕ Copy K

/-- Edges: the slots of the gates of `K` and the incoming edges of the copy vertices. -/
abbrev Edge := Slot K ⊕ Copy K

/-- The position of a slot among the slots of its signal. -/
noncomputable def slotIndex (t : Slot K) : Nat :=
  ((slots K (slotSignal K t)).equivFin ⟨t, (mem_slots K).mpr rfl⟩).val

theorem slotIndex_lt (t : Slot K) : slotIndex K t < fanout K (slotSignal K t) :=
  ((slots K (slotSignal K t)).equivFin ⟨t, (mem_slots K).mpr rfl⟩).isLt

private theorem equivFin_val_congr {w w' : Signal K} (h : w = w') (t : Slot K)
    (ht : t ∈ slots K w) (ht' : t ∈ slots K w') :
    ((slots K w).equivFin ⟨t, ht⟩).val = ((slots K w').equivFin ⟨t, ht'⟩).val := by
  subst h
  rfl

/-- Slots of one signal are determined by their positions. -/
theorem slotIndex_injective {t t' : Slot K} (hsignal : slotSignal K t = slotSignal K t')
    (hindex : slotIndex K t = slotIndex K t') : t = t' := by
  have ht' : t' ∈ slots K (slotSignal K t) := (mem_slots K).mpr hsignal.symm
  have : slotIndex K t = ((slots K (slotSignal K t)).equivFin ⟨t', ht'⟩).val :=
    hindex.trans (equivFin_val_congr K hsignal.symm t' _ _)
  have := (slots K (slotSignal K t)).equivFin.injective (Fin.ext this)
  exact Subtype.ext_iff.mp this

/-- The copy vertex at which a slot is attached, when its signal has fan-out at least two:
slots in order, with the last two slots sharing the last copy. -/
noncomputable def copyIndex (t : Slot K) : Nat :=
  min (slotIndex K t) (fanout K (slotSignal K t) - 2)

theorem copyIndex_lt (t : Slot K) (h : 2 ≤ fanout K (slotSignal K t)) :
    copyIndex K t < fanout K (slotSignal K t) - 1 := by
  unfold copyIndex
  omega

/-- The first endpoint of an edge: the signal vertex or copy vertex supplying it. -/
noncomputable def fst : Edge K → Vertex K
  | .inl t =>
      if h : 2 ≤ fanout K (slotSignal K t) then
        .inr ⟨slotSignal K t, ⟨copyIndex K t, copyIndex_lt K t h⟩⟩
      else .inl (slotSignal K t)
  | .inr ⟨w, k⟩ =>
      if h : k.val = 0 then .inl w
      else .inr ⟨w, ⟨k.val - 1, by omega⟩⟩

/-- The second endpoint of an edge: the gate owning a slot, or the copy vertex. -/
def snd : Edge K → Vertex K
  | .inl t => .inl (slotGate K t)
  | .inr c => .inr c

/-- The signal carried by an edge. -/
def signal : Edge K → Signal K
  | .inl t => slotSignal K t
  | .inr ⟨w, _⟩ => w

/-- The wire graph of `K`. -/
noncomputable def graph : Multigraph (Vertex K) (Edge K) where
  fst := fst K
  snd := snd K

theorem fst_inl_of_two_le (t : Slot K) (h : 2 ≤ fanout K (slotSignal K t)) :
    fst K (.inl t) = .inr ⟨slotSignal K t, ⟨copyIndex K t, copyIndex_lt K t h⟩⟩ := by
  simp [fst, h]

theorem fst_inl_of_not_two_le (t : Slot K) (h : ¬ 2 ≤ fanout K (slotSignal K t)) :
    fst K (.inl t) = .inl (slotSignal K t) := by
  simp [fst, h]

theorem fst_inr_zero (w : Signal K) (h : 0 < fanout K w - 1) :
    fst K (.inr ⟨w, ⟨0, h⟩⟩) = .inl w := by
  simp [fst]

theorem fst_inr_succ (w : Signal K) (k : Nat) (h : k + 1 < fanout K w - 1) :
    fst K (.inr ⟨w, ⟨k + 1, h⟩⟩) = .inr ⟨w, ⟨k, by omega⟩⟩ := by
  simp [fst]

/-! ## Walks along one signal -/

/-- Two vertices are joined by an edge carrying the signal `w`. -/
def SignalAdj (w : Signal K) (u v : Vertex K) : Prop :=
  ∃ e, signal K e = w ∧ ((fst K e = u ∧ snd K e = v) ∨ (fst K e = v ∧ snd K e = u))

/-- An edge joins its endpoints along its own signal. -/
theorem signalAdj_of_edge (e : Edge K) : SignalAdj K (signal K e) (fst K e) (snd K e) :=
  ⟨e, rfl, Or.inl ⟨rfl, rfl⟩⟩

theorem SignalAdj.symm {w : Signal K} {u v : Vertex K} (h : SignalAdj K w u v) :
    SignalAdj K w v u := by
  obtain ⟨e, he, h | h⟩ := h
  · exact ⟨e, he, Or.inr h⟩
  · exact ⟨e, he, Or.inl h⟩

theorem reflTransGen_signalAdj_symm {w : Signal K} {u v : Vertex K}
    (h : Relation.ReflTransGen (SignalAdj K w) u v) :
    Relation.ReflTransGen (SignalAdj K w) v u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.head (SignalAdj.symm K step) ih

/-- An edge carrying a signal is an edge of the graph. -/
theorem adj_of_signalAdj {w : Signal K} {u v : Vertex K} (h : SignalAdj K w u v) :
    (graph K).Adj u v := by
  obtain ⟨e, -, h⟩ := h
  exact ⟨e, h⟩

theorem reflTransGen_adj_of_signalAdj {w : Signal K} {u v : Vertex K}
    (h : Relation.ReflTransGen (SignalAdj K w) u v) :
    Relation.ReflTransGen (graph K).Adj u v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact ih.tail (adj_of_signalAdj K step)

/-- Every copy vertex of a signal is joined to the signal's vertex along its copy chain. -/
theorem signal_reaches_copy (w : Signal K) (m : Nat) (hm : m < fanout K w - 1) :
    Relation.ReflTransGen (SignalAdj K w) (.inl w) (.inr ⟨w, ⟨m, hm⟩⟩) := by
  induction m with
  | zero =>
    apply Relation.ReflTransGen.single
    have := signalAdj_of_edge K (.inr ⟨w, ⟨0, hm⟩⟩)
    rwa [fst_inr_zero] at this
  | succ m ih =>
    refine Relation.ReflTransGen.tail (ih (by omega)) ?_
    have := signalAdj_of_edge K (.inr ⟨w, ⟨m + 1, hm⟩⟩)
    rwa [fst_inr_succ] at this

/-- The vertex of a signal is joined to the vertex of every gate reading it, along edges
carrying the signal. -/
theorem signal_reaches_gate (t : Slot K) :
    Relation.ReflTransGen (SignalAdj K (slotSignal K t)) (.inl (slotSignal K t))
      (.inl (slotGate K t)) := by
  have toFst : Relation.ReflTransGen (SignalAdj K (slotSignal K t)) (.inl (slotSignal K t))
      (fst K (.inl t)) := by
    by_cases h₂ : 2 ≤ fanout K (slotSignal K t)
    · rw [fst_inl_of_two_le K t h₂]
      exact signal_reaches_copy K _ _ _
    · rw [fst_inl_of_not_two_le K t h₂]
  exact toFst.tail (signalAdj_of_edge K (.inl t))

/-- A walk along one signal between the two sides of a vertex set crosses its cut with an edge
carrying that signal. -/
theorem exists_mem_cut_of_reflTransGen (L : Finset (Vertex K)) {w : Signal K} {u v : Vertex K}
    (h : Relation.ReflTransGen (SignalAdj K w) u v) (huv : ¬ (u ∈ L ↔ v ∈ L)) :
    ∃ e ∈ (graph K).cut L, signal K e = w := by
  induction h with
  | refl => exact absurd Iff.rfl huv
  | @tail b c _ hbc ih =>
    by_cases hbcL : b ∈ L ↔ c ∈ L
    · exact ih fun hub => huv (hub.trans hbcL)
    · obtain ⟨e, he, hends⟩ := hbc
      refine ⟨e, ?_, he⟩
      rw [Multigraph.mem_cut]
      change ¬ (fst K e ∈ L ↔ snd K e ∈ L)
      rcases hends with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · rwa [h₁, h₂]
      · rw [h₁, h₂]
        exact fun h => hbcL h.symm

/-! ## Signals crossing a cut -/

/-- The wires of `K` whose vertices lie in `L`. -/
noncomputable def wiresIn (L : Finset (Vertex K)) : Finset (Wire n s) :=
  K.carrier.filter fun w => ∃ h : w ∈ K.carrier, (Sum.inl ⟨w, h⟩ : Vertex K) ∈ L

theorem mem_wiresIn {L : Finset (Vertex K)} {w : Wire n s} :
    w ∈ wiresIn K L ↔ ∃ h : w ∈ K.carrier, (Sum.inl ⟨w, h⟩ : Vertex K) ∈ L := by
  simp only [wiresIn, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

theorem wiresIn_subset (L : Finset (Vertex K)) : wiresIn K L ⊆ K.carrier :=
  fun _ hw => (mem_wiresIn K).mp hw |>.1

/-- A gate of `K` reading a wire on the other side of the split yields a cut edge carrying that
wire's signal. -/
theorem exists_cut_edge (L : Finset (Vertex K)) {g : Fin s} {w : Wire n s} (hr : p.Reads g w)
    (hg : Wire.gate g ∈ K.carrier)
    (hside : ¬ (w ∈ wiresIn K L ↔ Wire.gate g ∈ wiresIn K L)) :
    ∃ e ∈ (graph K).cut L, (signal K e).1 = w := by
  obtain ⟨a, ha⟩ := hr
  let t : Slot K := ⟨⟨g, a⟩, hg⟩
  have hsig : (slotSignal K t).1 = w := ha
  obtain ⟨e, he, hsig'⟩ := exists_mem_cut_of_reflTransGen K L (signal_reaches_gate K t) (by
    intro hiff
    apply hside
    have hw : w ∈ wiresIn K L ↔ (Sum.inl (slotSignal K t) : Vertex K) ∈ L := by
      rw [mem_wiresIn]
      constructor
      · rintro ⟨h, hL⟩
        have : slotSignal K t = ⟨w, h⟩ := Subtype.ext hsig
        rwa [this]
      · intro hL
        refine ⟨hsig ▸ (slotSignal K t).2, ?_⟩
        have : (⟨w, hsig ▸ (slotSignal K t).2⟩ : Signal K) = slotSignal K t :=
          Subtype.ext hsig.symm
        rwa [this]
    have hgate : Wire.gate g ∈ wiresIn K L ↔ (Sum.inl (slotGate K t) : Vertex K) ∈ L := by
      rw [mem_wiresIn]
      exact ⟨fun ⟨_, hL⟩ => hL, fun hL => ⟨hg, hL⟩⟩
    rw [hw, hgate]
    exact hiff)
  exact ⟨e, he, by rw [hsig', hsig]⟩

/-- **Crossing signals are bounded by the cut.** For every set `L` of vertices, the forward and
backward signals of the wires whose vertices lie in `L` number at most the edges of the cut
of `L`. -/
theorem card_forward_add_card_backward_le (L : Finset (Vertex K)) :
    (forward p (wiresIn K L)).card + (backward p (wiresIn K L)).card ≤
      ((graph K).cut L).card := by
  have hdisj : Disjoint (forward p (wiresIn K L)) (backward p (wiresIn K L)) := by
    rw [Finset.disjoint_left]
    intro w hf hb
    exact (mem_backward.mp hb).1 (mem_forward.mp hf).1
  rw [← Finset.card_union_of_disjoint hdisj]
  have hsub : forward p (wiresIn K L) ∪ backward p (wiresIn K L) ⊆
      ((graph K).cut L).image fun e => (signal K e).1 := by
    intro w hw
    rw [Finset.mem_image]
    rcases Finset.mem_union.mp hw with hf | hb
    · obtain ⟨hwP, g, hgP, hr⟩ := mem_forward.mp hf
      have hwK := wiresIn_subset K L hwP
      have hgK : Wire.gate g ∈ K.carrier := (K.closed g w hr).mpr hwK
      exact exists_cut_edge K L hr hgK (by tauto)
    · obtain ⟨hwP, g, hgP, hr⟩ := mem_backward.mp hb
      have hgK := wiresIn_subset K L hgP
      exact exists_cut_edge K L hr hgK (by tauto)
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

/-! ## Graph properties -/

/-- No edge joins a vertex to itself. -/
theorem loopless : (graph K).Loopless := by
  rintro (t | ⟨w, k⟩)
  · change fst K (.inl t) ≠ snd K (.inl t)
    by_cases h₂ : 2 ≤ fanout K (slotSignal K t)
    · rw [fst_inl_of_two_le K t h₂]
      simp [snd]
    · rw [fst_inl_of_not_two_le K t h₂]
      simp only [snd, ne_eq, Sum.inl.injEq]
      intro h
      have := congrArg (fun w : Signal K => w.1.index.val) h
      simp only [slotSignal, slotGate, slotWire, Cslib.Circuits.Wire.index_gate,
        Fin.val_natAdd] at this
      have := p.lines_wires_lt t.1.1 t.1.2
      omega
  · change fst K (.inr ⟨w, k⟩) ≠ snd K (.inr ⟨w, k⟩)
    by_cases h₀ : k.val = 0
    · simp [fst, snd, h₀]
    · simp only [fst, snd, h₀, ↓reduceDIte, ne_eq, Sum.inr.injEq]
      intro h
      have := congrArg (fun c : Copy K => c.2.val) h
      simp only at this
      omega

/-- The edges leaving a vertex. -/
noncomputable def outEdges (v : Vertex K) : Finset (Edge K) :=
  Finset.univ.filter fun e => fst K e = v

/-- The edges entering a vertex. -/
noncomputable def inEdges (v : Vertex K) : Finset (Edge K) :=
  Finset.univ.filter fun e => snd K e = v

theorem mem_outEdges {v : Vertex K} {e : Edge K} : e ∈ outEdges K v ↔ fst K e = v := by
  simp [outEdges]

theorem mem_inEdges {v : Vertex K} {e : Edge K} : e ∈ inEdges K v ↔ snd K e = v := by
  simp [inEdges]

theorem edgesAt_subset (v : Vertex K) :
    (graph K).edgesAt v ⊆ outEdges K v ∪ inEdges K v := by
  intro e he
  rcases (Multigraph.mem_edgesAt _).mp he with h | h
  · exact Finset.mem_union_left _ ((mem_outEdges K).mpr h)
  · exact Finset.mem_union_right _ ((mem_inEdges K).mpr h)

/-- A signal vertex receives at most two edges: the slots of its gate. -/
theorem card_inEdges_inl_le (hp : p.FanInAtMost 2) (w : Signal K) :
    (inEdges K (.inl w)).card ≤ 2 := by
  let φ : Edge K → Nat := fun e => match e with
    | .inl t => t.1.2.val
    | .inr _ => 0
  have maps : Set.MapsTo φ ↑(inEdges K (.inl w)) ↑(Finset.range 2) := by
    rintro (t | c) ht
    · simp only [Finset.coe_range, Set.mem_Iio, φ]
      exact lt_of_lt_of_le t.1.2.isLt (arity_le_of_fanInAtMost p hp t.1.1)
    · exact absurd ((mem_inEdges K).mp (Finset.mem_coe.mp ht)) (by simp [snd])
  have inj : Set.InjOn φ ↑(inEdges K (.inl w)) := by
    rintro (t | c) ht (t' | c') ht' heq
    · have h1 : slotGate K t = w := Sum.inl.inj ((mem_inEdges K).mp (Finset.mem_coe.mp ht))
      have h2 : slotGate K t' = w := Sum.inl.inj ((mem_inEdges K).mp (Finset.mem_coe.mp ht'))
      have hgate : t.1.1 = t'.1.1 :=
        Cslib.Circuits.Wire.gate.inj (Subtype.ext_iff.mp (h1.trans h2.symm))
      obtain ⟨⟨g, a⟩, hg⟩ := t
      obtain ⟨⟨g', a'⟩, hg'⟩ := t'
      simp only at hgate
      subst hgate
      have : a = a' := Fin.ext heq
      subst this
      rfl
    · exact absurd ((mem_inEdges K).mp (Finset.mem_coe.mp ht')) (by simp [snd])
    · exact absurd ((mem_inEdges K).mp (Finset.mem_coe.mp ht)) (by simp [snd])
    · exact absurd ((mem_inEdges K).mp (Finset.mem_coe.mp ht)) (by simp [snd])
  simpa using Finset.card_le_card_of_injOn φ maps inj

/-- At most one edge leaves a signal vertex. -/
theorem card_outEdges_inl_le (w : Signal K) : (outEdges K (.inl w)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  rintro (t | ⟨w₁, k₁⟩) he (t' | ⟨w₂, k₂⟩) he'
  · have h := (mem_outEdges K).mp he
    have h' := (mem_outEdges K).mp he'
    by_cases h₂ : 2 ≤ fanout K (slotSignal K t)
    · rw [fst_inl_of_two_le K t h₂] at h
      exact absurd h (by simp)
    by_cases h₂' : 2 ≤ fanout K (slotSignal K t')
    · rw [fst_inl_of_two_le K t' h₂'] at h'
      exact absurd h' (by simp)
    rw [fst_inl_of_not_two_le K t h₂, Sum.inl.injEq] at h
    rw [fst_inl_of_not_two_le K t' h₂', Sum.inl.injEq] at h'
    have hone : fanout K w ≤ 1 := by
      have := h ▸ (show ¬ 2 ≤ fanout K (slotSignal K t) from h₂)
      omega
    rw [Finset.card_le_one.mp hone t ((mem_slots K).mpr h) t' ((mem_slots K).mpr h')]
  · exfalso
    have h := (mem_outEdges K).mp he
    have h' := (mem_outEdges K).mp he'
    by_cases h₂ : 2 ≤ fanout K (slotSignal K t)
    · rw [fst_inl_of_two_le K t h₂] at h
      exact absurd h (by simp)
    rw [fst_inl_of_not_two_le K t h₂, Sum.inl.injEq] at h
    by_cases h₀ : k₂.val = 0
    · simp only [fst, h₀, ↓reduceDIte, Sum.inl.injEq] at h'
      subst h'
      have := k₂.isLt
      rw [h] at h₂
      omega
    · simp [fst, h₀] at h'
  · exfalso
    have h := (mem_outEdges K).mp he
    have h' := (mem_outEdges K).mp he'
    by_cases h₂ : 2 ≤ fanout K (slotSignal K t')
    · rw [fst_inl_of_two_le K t' h₂] at h'
      exact absurd h' (by simp)
    rw [fst_inl_of_not_two_le K t' h₂, Sum.inl.injEq] at h'
    by_cases h₀ : k₁.val = 0
    · simp only [fst, h₀, ↓reduceDIte, Sum.inl.injEq] at h
      subst h
      have := k₁.isLt
      rw [h'] at h₂
      omega
    · simp [fst, h₀] at h
  · have h := (mem_outEdges K).mp he
    have h' := (mem_outEdges K).mp he'
    by_cases h₀ : k₁.val = 0
    · by_cases h₀' : k₂.val = 0
      · simp only [fst, h₀, h₀', ↓reduceDIte, Sum.inl.injEq] at h h'
        subst h h'
        congr 2
        exact Fin.ext (h₀.trans h₀'.symm)
      · simp [fst, h₀'] at h'
    · simp [fst, h₀] at h

/-- Exactly one edge enters a copy vertex. -/
theorem card_inEdges_inr_le (c : Copy K) : (inEdges K (.inr c)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  rintro (t | c') he (t' | c'') he'
  · exact absurd ((mem_inEdges K).mp he) (by simp [snd])
  · exact absurd ((mem_inEdges K).mp he) (by simp [snd])
  · exact absurd ((mem_inEdges K).mp he') (by simp [snd])
  · have h1 : c' = c := Sum.inr.inj ((mem_inEdges K).mp he)
    have h2 : c'' = c := Sum.inr.inj ((mem_inEdges K).mp he')
    rw [h1, h2]

/-- A slot attached to a copy vertex has its position at least the copy's. -/
theorem copyIndex_le_slotIndex (t : Slot K) : copyIndex K t ≤ slotIndex K t :=
  Nat.min_le_left _ _

/-- At most two edges leave a copy vertex: the next copy edge and its slots. -/
theorem card_outEdges_inr_le (w : Signal K) (k : Fin (fanout K w - 1)) :
    (outEdges K (.inr ⟨w, k⟩)).card ≤ 2 := by
  have slotMem : ∀ t : Slot K, .inl t ∈ outEdges K (.inr ⟨w, k⟩) →
      slotSignal K t = w ∧ 2 ≤ fanout K w ∧ copyIndex K t = k.val := by
    intro t ht
    have h := (mem_outEdges K).mp ht
    by_cases h₂ : 2 ≤ fanout K (slotSignal K t)
    · rw [fst_inl_of_two_le K t h₂] at h
      simp only [Sum.inr.injEq, Sigma.mk.inj_iff] at h
      obtain ⟨hw, hk⟩ := h
      subst hw
      exact ⟨rfl, h₂, Fin.ext_iff.mp (eq_of_heq hk)⟩
    · rw [fst_inl_of_not_two_le K t h₂] at h
      exact absurd h (by simp)
  have copyMem : ∀ (w' : Signal K) (k' : Fin (fanout K w' - 1)),
      .inr ⟨w', k'⟩ ∈ outEdges K (.inr ⟨w, k⟩) → w' = w ∧ k'.val = k.val + 1 := by
    intro w' k' h
    have h := (mem_outEdges K).mp h
    by_cases h₀ : k'.val = 0
    · simp [fst, h₀] at h
    · simp only [fst, h₀, ↓reduceDIte, Sum.inr.injEq, Sigma.mk.inj_iff] at h
      obtain ⟨hw, hk⟩ := h
      subst hw
      have := Fin.ext_iff.mp (eq_of_heq hk)
      simp only at this
      exact ⟨rfl, by omega⟩
  let φ : Edge K → Nat := fun e => match e with
    | .inl t => slotIndex K t - k.val
    | .inr _ => 1
  have maps : Set.MapsTo φ ↑(outEdges K (.inr ⟨w, k⟩)) ↑(Finset.range 2) := by
    rintro (t | ⟨w', k'⟩) he
    · obtain ⟨hw, h₂, hk⟩ := slotMem t (Finset.mem_coe.mp he)
      have hlt := slotIndex_lt K t
      rw [hw] at hlt
      have hmin : min (slotIndex K t) (fanout K w - 2) = k.val := by
        rw [← hk, copyIndex, hw]
      simp only [Finset.coe_range, Set.mem_Iio, φ]
      omega
    · simp [φ]
  have inj : Set.InjOn φ ↑(outEdges K (.inr ⟨w, k⟩)) := by
    rintro (t | ⟨w', k'⟩) he (t' | ⟨w'', k''⟩) he' heq
    · obtain ⟨hw, h₂, hk⟩ := slotMem t (Finset.mem_coe.mp he)
      obtain ⟨hw', _, hk'⟩ := slotMem t' (Finset.mem_coe.mp he')
      have hle := copyIndex_le_slotIndex K t
      have hle' := copyIndex_le_slotIndex K t'
      have : slotIndex K t = slotIndex K t' := by
        simp only [φ] at heq
        omega
      rw [slotIndex_injective K (hw.trans hw'.symm) this]
    · obtain ⟨hw, h₂, hk⟩ := slotMem t (Finset.mem_coe.mp he)
      obtain ⟨hw'', hk''⟩ := copyMem w'' k'' (Finset.mem_coe.mp he')
      subst hw''
      have hlt := k''.isLt
      have hle := copyIndex_le_slotIndex K t
      have hmin : min (slotIndex K t) (fanout K w'' - 2) = k.val := by
        rw [← hk, copyIndex, hw]
      simp only [φ] at heq
      omega
    · obtain ⟨hw, hk⟩ := copyMem w' k' (Finset.mem_coe.mp he)
      obtain ⟨hw', h₂, hk'⟩ := slotMem t' (Finset.mem_coe.mp he')
      subst hw
      have hlt := k'.isLt
      have hle := copyIndex_le_slotIndex K t'
      have hmin : min (slotIndex K t') (fanout K w' - 2) = k.val := by
        rw [← hk', copyIndex, hw']
      simp only [φ] at heq
      omega
    · obtain ⟨hw, hk⟩ := copyMem w' k' (Finset.mem_coe.mp he)
      obtain ⟨hw', hk'⟩ := copyMem w'' k'' (Finset.mem_coe.mp he')
      subst hw hw'
      congr 2
      exact Fin.ext (hk.trans hk'.symm)
  simpa using Finset.card_le_card_of_injOn φ maps inj

/-- Every vertex has at most three incident edges. -/
theorem maxDegreeLE_three (hp : p.FanInAtMost 2) : (graph K).MaxDegreeLE 3 := by
  intro v
  refine (Finset.card_le_card (edgesAt_subset K v)).trans
    ((Finset.card_union_le _ _).trans ?_)
  rcases v with w | ⟨w, k⟩
  · exact add_le_add (card_outEdges_inl_le K w) (card_inEdges_inl_le K hp w)
  · exact add_le_add (card_outEdges_inr_le K w k) (card_inEdges_inr_le K ⟨w, k⟩)

/-- Linked wires of `K` are joined in the wire graph. -/
theorem reflTransGen_adj_of_linked {u v : Wire n s} (h : Linked p u v) (hu : u ∈ K.carrier)
    (hv : v ∈ K.carrier) :
    Relation.ReflTransGen (graph K).Adj (.inl ⟨u, hu⟩) (.inl ⟨v, hv⟩) := by
  rcases h with ⟨g, rfl, a, ha⟩ | ⟨g, rfl, a, ha⟩
  · let t : Slot K := ⟨⟨g, a⟩, hu⟩
    have hsig : slotSignal K t = ⟨v, hv⟩ := Subtype.ext ha
    have := reflTransGen_adj_of_signalAdj K (signal_reaches_gate K t)
    rw [hsig] at this
    exact Multigraph.reflTransGen_adj_symm this
  · let t : Slot K := ⟨⟨g, a⟩, hv⟩
    have hsig : slotSignal K t = ⟨u, hu⟩ := Subtype.ext ha
    have := reflTransGen_adj_of_signalAdj K (signal_reaches_gate K t)
    rw [hsig] at this
    exact this

/-- Paths of linked wires starting in `K` stay in `K` and lift to the wire graph. -/
theorem exists_reflTransGen_adj_of_reflTransGen {u v : Wire n s}
    (h : Relation.ReflTransGen (Linked p) u v) (hu : u ∈ K.carrier) :
    ∃ hv : v ∈ K.carrier,
      Relation.ReflTransGen (graph K).Adj (.inl ⟨u, hu⟩) (.inl ⟨v, hv⟩) := by
  induction h with
  | refl => exact ⟨hu, Relation.ReflTransGen.refl⟩
  | @tail b c _ hbc ih =>
    obtain ⟨hb, path⟩ := ih
    have hc : c ∈ K.carrier := by
      rcases hbc with ⟨g, rfl, hr⟩ | ⟨g, rfl, hr⟩
      · exact (K.closed g c hr).mp hb
      · exact (K.closed g b hr).mpr hb
    exact ⟨hc, path.trans (reflTransGen_adj_of_linked K hbc hb hc)⟩

/-- The wire graph of a nonempty set of wires connected in the program's wire graph is
connected. -/
theorem connected (hne : K.carrier.Nonempty)
    (hconn : ∀ u ∈ K.carrier, ∀ v ∈ K.carrier, Relation.ReflTransGen (Linked p) u v) :
    (graph K).Connected := by
  obtain ⟨w₀, hw₀⟩ := hne
  apply Multigraph.connected_of_forall_reflTransGen (Sum.inl ⟨w₀, hw₀⟩)
  have signal_root : ∀ v : Signal K,
      Relation.ReflTransGen (graph K).Adj (.inl v) (.inl ⟨w₀, hw₀⟩) := by
    intro v
    obtain ⟨_, path⟩ := exists_reflTransGen_adj_of_reflTransGen K (hconn w₀ hw₀ v.1 v.2) hw₀
    exact Multigraph.reflTransGen_adj_symm path
  rintro (v | ⟨w, k⟩)
  · exact signal_root v
  · exact (Multigraph.reflTransGen_adj_symm
      (reflTransGen_adj_of_signalAdj K (signal_reaches_copy K w k.val k.isLt))).trans
      (signal_root w)

/-! ## Counting vertices and edges -/

/-- The slots of `K` number at most twice its gates. -/
theorem card_slot_le (hp : p.FanInAtMost 2) :
    Fintype.card (Slot K) ≤ 2 * (gatesIn K.carrier).card := by
  let φ : Slot K → Fin s × Fin 2 := fun t =>
    (t.1.1, ⟨t.1.2.val, lt_of_lt_of_le t.1.2.isLt (arity_le_of_fanInAtMost p hp t.1.1)⟩)
  have maps : Set.MapsTo φ ↑(Finset.univ : Finset (Slot K))
      ↑(gatesIn K.carrier ×ˢ (Finset.univ : Finset (Fin 2))) := by
    intro t _
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_univ, and_true, φ]
    simp only [gatesIn, Finset.mem_filter, Finset.mem_univ, true_and]
    exact t.2
  have inj : Set.InjOn φ ↑(Finset.univ : Finset (Slot K)) := by
    rintro ⟨⟨g, a⟩, hg⟩ _ ⟨⟨g', a'⟩, hg'⟩ _ heq
    simp only [Prod.mk.injEq, Fin.mk.injEq, φ] at heq
    obtain ⟨rfl, ha⟩ := heq
    have : a = a' := Fin.ext ha
    subst this
    rfl
  have := Finset.card_le_card_of_injOn φ maps inj
  rw [Finset.card_univ, Finset.card_product, Finset.card_univ, Fintype.card_fin] at this
  omega

/-- The signals of `K` are its inputs and its gates. -/
theorem card_signal :
    Fintype.card (Signal K) = (inputsIn K.carrier).card + (gatesIn K.carrier).card := by
  rw [Fintype.card_subtype, inputsIn, gatesIn, Finset.card_filter, Finset.card_filter,
    Finset.card_filter]
  exact (Fintype.sum_equiv (Wire.equiv n s) _ (Sum.elim _ _)
    (fun w => by cases w <;> rfl)).trans (Fintype.sum_sum_type _)

/-- There are no more copy vertices than slots. -/
theorem card_copy_le : Fintype.card (Copy K) ≤ Fintype.card (Slot K) := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  calc ∑ w : Signal K, (fanout K w - 1)
      ≤ ∑ w : Signal K, fanout K w := Finset.sum_le_sum fun w _ => Nat.sub_le _ _
    _ = Fintype.card (Slot K) := by
      rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise
        (f := slotSignal K) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
      rfl

/-- The excess of edges over vertices is at most the gates minus the inputs of `K`. -/
theorem card_edge_sub_card_vertex_le (hp : p.FanInAtMost 2) :
    (Fintype.card (Edge K) : ℝ) - Fintype.card (Vertex K) ≤
      ((gatesIn K.carrier).card : ℝ) - (inputsIn K.carrier).card := by
  have h₁ := card_slot_le K hp
  have h₂ := card_signal K
  have hE : (Fintype.card (Edge K) : ℝ) = Fintype.card (Slot K) + Fintype.card (Copy K) := by
    rw [Fintype.card_sum]
    push_cast
    ring
  have hV : (Fintype.card (Vertex K) : ℝ) = Fintype.card (Signal K) + Fintype.card (Copy K) := by
    rw [Fintype.card_sum]
    push_cast
    ring
  have h₁' : (Fintype.card (Slot K) : ℝ) ≤ 2 * (gatesIn K.carrier).card := by exact_mod_cast h₁
  have h₂' : (Fintype.card (Signal K) : ℝ) =
      (inputsIn K.carrier).card + (gatesIn K.carrier).card := by exact_mod_cast h₂
  rw [hE, hV]
  linarith

/-- The wire graph of `K` has at most `i + 3 g` vertices for `i` inputs and `g` gates in `K`. -/
theorem card_vertex_le (hp : p.FanInAtMost 2) :
    Fintype.card (Vertex K) ≤ (inputsIn K.carrier).card + 3 * (gatesIn K.carrier).card := by
  have h₁ := card_slot_le K hp
  have h₂ := card_signal K
  have h₃ := card_copy_le K
  rw [Fintype.card_sum]
  omega

end WireGraph

end Algebraic.Cutwidth.MultiOutput.Internal
