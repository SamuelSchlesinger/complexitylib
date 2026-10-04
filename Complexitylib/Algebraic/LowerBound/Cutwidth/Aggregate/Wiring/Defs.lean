/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Ordering.Internal.Graph
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Network
public import Complexitylib.Algebraic.LowerBound.Cutwidth.SingleCut.Internal

/-!
# Local evaluation on a closed wire graph

The graph has no extra edges for observed sinks. Gate values are computed directly from
their incident argument slots, including nullary gates. Inputs use their first outgoing
edge; the compiler therefore assumes that the selected inputs have positive fanout.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Wiring

open scoped Classical
open MultiOutput.Internal
open WireGraph

variable {σ : Signature} {n s : Nat} {p : Program σ n s} (K : ClosedSet p)

/-- Every selected primary input has an ordinary outgoing slot. -/
def InputsHaveFanout : Prop :=
  ∀ (j : Fin n) (h : Wire.input j ∈ K.carrier), 0 < fanout K ⟨Wire.input j, h⟩

/-- The signal carried by an edge leaving a signal vertex. -/
theorem signal_eq_of_fst_eq_inl {e : Edge K} {w : Signal K}
    (h : fst K e = .inl w) : signal K e = w := by
  rcases e with t | ⟨w', k⟩
  · by_cases h₂ : 2 ≤ fanout K (slotSignal K t)
    · simp [fst, h₂] at h
    · simpa [fst, h₂, signal] using h
  · by_cases h₀ : k.val = 0
    · simpa [fst, h₀, signal] using h
    · simp [fst, h₀] at h

/-- The signal carried by an edge leaving a copy vertex. -/
theorem signal_eq_of_fst_eq_inr {e : Edge K} {c : Copy K}
    (h : fst K e = .inr c) : signal K e = c.1 := by
  rcases e with t | ⟨w, k⟩
  · by_cases h₂ : 2 ≤ fanout K (slotSignal K t)
    · rw [fst_inl_of_two_le K t h₂] at h
      exact congrArg Sigma.fst (Sum.inr.inj h)
    · simp [fst, h₂] at h
  · by_cases h₀ : k.val = 0
    · simp [fst, h₀] at h
    · simp only [fst, h₀, ↓reduceDIte, Sum.inr.injEq] at h
      exact congrArg Sigma.fst h

/-- A signal with positive fanout has an outgoing edge at its signal vertex. -/
theorem exists_outgoing (w : Signal K) (hpos : 0 < fanout K w) :
    ∃ e : Edge K, fst K e = .inl w := by
  by_cases h₂ : 2 ≤ fanout K w
  · exact ⟨.inr ⟨w, ⟨0, by lia⟩⟩, fst_inr_zero K w (by lia)⟩
  · obtain ⟨t, ht⟩ := Finset.card_pos.mp hpos
    have hs := (mem_slots K).mp ht
    exact ⟨.inl t, by rw [fst_inl_of_not_two_le K t (by simpa [hs] using h₂), hs]⟩

variable [Nonempty (Edge K)]

/-- An outgoing edge, with an irrelevant default for sinks. -/
noncomputable def firstOut (w : Signal K) : Edge K :=
  if h : 0 < fanout K w then (exists_outgoing K w h).choose else Classical.arbitrary _

theorem fst_firstOut (w : Signal K) (h : 0 < fanout K w) :
    fst K (firstOut K w) = .inl w := by
  simp only [firstOut, h, ↓reduceDIte]
  exact (exists_outgoing K w h).choose_spec

theorem signal_firstOut (w : Signal K) (h : 0 < fanout K w) :
    signal K (firstOut K w) = w := signal_eq_of_fst_eq_inl K (fst_firstOut K w h)

/-- At most one outgoing edge at a signal vertex identifies its chosen edge. -/
theorem eq_firstOut_of_fst_eq_inl {w : Signal K} {e : Edge K}
    (h : fst K e = .inl w) (hpos : 0 < fanout K w) : e = firstOut K w :=
  Finset.card_le_one.mp (card_outEdges_inl_le K w) _ ((mem_outEdges K).mpr h)
    _ ((mem_outEdges K).mpr (fst_firstOut K w hpos))

/-- The value of a gate, computed from its incident argument slots. -/
def opValue (I : Interpretation σ Bool) (g : Fin s) (h : Wire.gate g ∈ K.carrier)
    (α : Edge K → Bool) : Bool :=
  I (p.lines g).op fun a => α (.inl ⟨⟨g, a⟩, h⟩)

/-- The value observed at a signal vertex, including gates without outgoing edges. -/
noncomputable def localValue (I : Interpretation σ Bool) (α : Edge K → Bool) : Signal K → Bool
  | ⟨.input j, h⟩ => α (firstOut K ⟨.input j, h⟩)
  | ⟨.gate g, h⟩ => opValue K I g h α

/-- Every outgoing edge agrees with its local signal or incoming copy edge. -/
noncomputable def Check (I : Interpretation σ Bool) : Vertex K → (Edge K → Bool) → Prop
  | .inl w, α => ∀ e, fst K e = .inl w → α e = localValue K I α w
  | .inr c, α => ∀ e, fst K e = .inr c → α e = α (.inr c)

/-- Each selected input is read at its signal vertex. -/
noncomputable def portVertex (j : Fin n) : Vertex K :=
  if h : Wire.input j ∈ K.carrier then .inl ⟨Wire.input j, h⟩
  else fst K (Classical.arbitrary (Edge K))

/-- The chosen outgoing edge carries a selected input. -/
noncomputable def portEdge (j : Fin n) : Edge K :=
  if h : Wire.input j ∈ K.carrier then firstOut K ⟨Wire.input j, h⟩
  else Classical.arbitrary _

/-- Local values depend only on incident edge bits. -/
theorem localValue_congr (hinput : InputsHaveFanout K) (I : Interpretation σ Bool)
    (w : Signal K) (α β : Edge K → Bool)
    (h : ∀ e, fst K e = .inl w ∨ snd K e = .inl w → α e = β e) :
    localValue K I α w = localValue K I β w := by
  obtain ⟨w, hw⟩ := w
  cases w with
  | input j => exact h _ (Or.inl (fst_firstOut K _ (hinput j hw)))
  | gate g =>
    apply congrArg (I (p.lines g).op)
    funext a
    exact h (.inl ⟨⟨g, a⟩, hw⟩) (Or.inr rfl)

/-- The unchanged wire graph equipped with local evaluation checks and input ports. -/
noncomputable def network (hinput : InputsHaveFanout K) (I : Interpretation σ Bool) :
    Network n (Vertex K) (Edge K) where
  fst := fst K
  snd := snd K
  Check := Check K I
  check_local := by
    rintro (w | c) α β agree check e he
    · rw [← agree e (Or.inl he), check e he]
      exact localValue_congr K hinput I w α β agree
    · rw [← agree e (Or.inl he), ← agree (.inr c) (Or.inr rfl)]
      exact check e he
  read := SingleCut.inputsIn K.carrier
  portVertex := portVertex K
  portEdge := portEdge K
  port_incident := by
    intro j hj
    have hj' : Wire.input j ∈ K.carrier := by
      simpa [SingleCut.inputsIn] using hj
    simpa [portVertex, portEdge, hj'] using
      Or.inl (b := snd K (firstOut K ⟨Wire.input j, hj'⟩) = .inl ⟨Wire.input j, hj'⟩)
        (fst_firstOut K _ (hinput j hj'))

end Algebraic.Cutwidth.Aggregate.Wiring
