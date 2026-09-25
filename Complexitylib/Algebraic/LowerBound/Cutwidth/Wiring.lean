/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.Binary
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Network
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Algebra.BigOperators.Fin

/-!
# The wiring graph of a binary circuit

Fix a program over the full binary basis and an output gate. The *reachable*
wires are the output gate and, recursively, the argument wires of reachable
gates. The wiring graph has a vertex for every reachable wire and, for a
signal feeding `f ≥ 2` gate slots, `f - 1` copy vertices of degree three
through which the signal is routed. Its edges are the slots of reachable
gates and the incoming edge of every copy vertex.

Each edge carries one bit. A gate vertex checks that its outgoing edge carries
the gate's function of its two slot bits, the output gate checks that this
value is `1`, and a copy vertex checks that all its incident edges agree. An
input vertex has no check; its outgoing edge is the port of the variable.

The main results are

* `network_computes`: an input is accepted by the circuit exactly when some
  edge assignment satisfies every check and every port;
* `loopless`, `maxDegreeLE_three`, `connected`: the multigraph hypotheses of
  the graph-ordering lemma;
* `card_edge_add_card_signal`, `card_slot`, `card_signal`, `card_copy_le`:
  the edge and vertex counts, giving `M - N = s' - n'` for `s'` reachable
  gates and `n'` reachable inputs.
-/

@[expose] public section

namespace Algebraic
namespace Cutwidth

open scoped Classical

/-- The argument wires of a widened binary line refer to earlier wires. -/
theorem lines_wires_lt {n s : Nat} (p : Program Binary.signature n s) (g : Fin s) (a : Fin 2) :
    ((p.lines g).wires a).val < n + g.val := by
  induction p with
  | empty => exact g.elim0
  | @gate k q line ih =>
    refine Fin.lastCases ?_ (fun j => ?_) g
    · rw [Program.lines_gate_last, Line.mapWires_wires, Wire.Renaming.castSucc_apply]
      simp
    · rw [Program.lines_gate_castSucc, Line.mapWires_wires, Wire.Renaming.castSucc_apply]
      simpa using ih j

namespace Wiring

variable {n s : Nat} (p : Program Binary.signature n s) (out : Fin s)

/-- A wire is reachable when it is the output gate or an argument of a reachable gate. -/
inductive Reach : Wire n s → Prop
  /-- The output gate is reachable. -/
  | out : Reach (Wire.gate out)
  /-- An argument of a reachable gate is reachable. -/
  | arg {g : Fin s} (a : Fin 2) : Reach (Wire.gate g) → Reach ((p.lines g).wires a)

/-- The reachable wires: the signals of the wiring graph. -/
abbrev Signal := {w : Wire n s // Reach p out w}

/-- The argument slots of reachable gates. -/
abbrev Slot := {t : Fin s × Fin 2 // Reach p out (Wire.gate t.1)}

/-- Reachability is decided classically; the graph is a proof object. -/
noncomputable instance : Fintype (Signal p out) := Subtype.fintype _

noncomputable instance : Fintype (Slot p out) := Subtype.fintype _

/-- The signal read by a slot. -/
def slotSignal (t : Slot p out) : Signal p out :=
  ⟨(p.lines t.1.1).wires t.1.2, Reach.arg t.1.2 t.2⟩

/-- The gate owning a slot. -/
def slotGate (t : Slot p out) : Signal p out :=
  ⟨Wire.gate t.1.1, t.2⟩

/-- The slots fed by a signal. -/
noncomputable def slots (w : Signal p out) : Finset (Slot p out) :=
  Finset.univ.filter fun t => slotSignal p out t = w

theorem mem_slots {w : Signal p out} {t : Slot p out} :
    t ∈ slots p out w ↔ slotSignal p out t = w := by
  simp [slots]

/-- The number of slots fed by a signal. -/
noncomputable def fanout (w : Signal p out) : Nat :=
  (slots p out w).card

theorem fanout_pos_of_slot (t : Slot p out) : 0 < fanout p out (slotSignal p out t) :=
  Finset.card_pos.mpr ⟨t, (mem_slots p out).mpr rfl⟩

/-- A signal feeding `f ≥ 2` slots is routed through `f - 1` copy vertices. -/
abbrev Copy := Σ w : Signal p out, Fin (fanout p out w - 1)

/-- Vertices: reachable wires and copy vertices. -/
abbrev Vertex := Signal p out ⊕ Copy p out

/-- Edges: slots of reachable gates and the incoming edges of copy vertices. -/
abbrev Edge := Slot p out ⊕ Copy p out

/-- The position of a slot among the slots of its signal. -/
noncomputable def slotIndex (t : Slot p out) : Nat :=
  ((slots p out (slotSignal p out t)).equivFin ⟨t, (mem_slots p out).mpr rfl⟩).val

theorem slotIndex_lt (t : Slot p out) : slotIndex p out t < fanout p out (slotSignal p out t) :=
  ((slots p out (slotSignal p out t)).equivFin ⟨t, (mem_slots p out).mpr rfl⟩).isLt

private theorem equivFin_val_congr {w w' : Signal p out} (h : w = w') (t : Slot p out)
    (ht : t ∈ slots p out w) (ht' : t ∈ slots p out w') :
    ((slots p out w).equivFin ⟨t, ht⟩).val = ((slots p out w').equivFin ⟨t, ht'⟩).val := by
  subst h
  rfl

/-- Slots of one signal are determined by their positions. -/
theorem slotIndex_injective {t t' : Slot p out}
    (hsignal : slotSignal p out t = slotSignal p out t')
    (hindex : slotIndex p out t = slotIndex p out t') : t = t' := by
  have ht' : t' ∈ slots p out (slotSignal p out t) := (mem_slots p out).mpr hsignal.symm
  have : slotIndex p out t = ((slots p out (slotSignal p out t)).equivFin ⟨t', ht'⟩).val :=
    hindex.trans (equivFin_val_congr p out hsignal.symm t' _ _)
  have := (slots p out (slotSignal p out t)).equivFin.injective (Fin.ext this)
  exact Subtype.ext_iff.mp this

/-- The copy vertex at which a slot is attached, when its signal has fan-out at
least two: slots in order, with the last two slots sharing the last copy. -/
noncomputable def copyIndex (t : Slot p out) : Nat :=
  min (slotIndex p out t) (fanout p out (slotSignal p out t) - 2)

theorem copyIndex_lt (t : Slot p out) (h : 2 ≤ fanout p out (slotSignal p out t)) :
    copyIndex p out t < fanout p out (slotSignal p out t) - 1 := by
  unfold copyIndex
  omega

/-- The first endpoint of an edge: the signal vertex or copy vertex supplying it. -/
noncomputable def fst : Edge p out → Vertex p out
  | .inl t =>
      if h : 2 ≤ fanout p out (slotSignal p out t) then
        .inr ⟨slotSignal p out t, ⟨copyIndex p out t, copyIndex_lt p out t h⟩⟩
      else .inl (slotSignal p out t)
  | .inr ⟨w, k⟩ =>
      if h : k.val = 0 then .inl w
      else .inr ⟨w, ⟨k.val - 1, by omega⟩⟩

/-- The second endpoint of an edge: the gate reading a slot, or the copy vertex. -/
def snd : Edge p out → Vertex p out
  | .inl t => .inl (slotGate p out t)
  | .inr c => .inr c

/-- The signal carried by an edge. -/
def signal : Edge p out → Signal p out
  | .inl t => slotSignal p out t
  | .inr ⟨w, _⟩ => w

/-- The first outgoing edge of a signal with positive fan-out: the incoming edge
of its first copy vertex, or its unique slot. -/
noncomputable def firstOut (w : Signal p out) : Edge p out :=
  if h : 2 ≤ fanout p out w then .inr ⟨w, ⟨0, by omega⟩⟩
  else if h' : 0 < fanout p out w then .inl ((slots p out w).equivFin.symm ⟨0, h'⟩).1
  else .inl ⟨(out, 0), Reach.out⟩

theorem fst_inl_of_two_le (t : Slot p out) (h : 2 ≤ fanout p out (slotSignal p out t)) :
    fst p out (.inl t) = .inr ⟨slotSignal p out t, ⟨copyIndex p out t, copyIndex_lt p out t h⟩⟩ := by
  simp [fst, h]

theorem fst_inl_of_fanout_eq_one (t : Slot p out) (h : fanout p out (slotSignal p out t) = 1) :
    fst p out (.inl t) = .inl (slotSignal p out t) := by
  have : ¬ 2 ≤ fanout p out (slotSignal p out t) := by omega
  simp [fst, this]

theorem fst_inr_zero (w : Signal p out) (h : 0 < fanout p out w - 1) :
    fst p out (.inr ⟨w, ⟨0, h⟩⟩) = .inl w := by
  simp [fst]

theorem fst_inr_succ (w : Signal p out) (k : Nat) (h : k + 1 < fanout p out w - 1) :
    fst p out (.inr ⟨w, ⟨k + 1, h⟩⟩) = .inr ⟨w, ⟨k, by omega⟩⟩ := by
  simp [fst]

theorem snd_inl (t : Slot p out) : snd p out (.inl t) = .inl (slotGate p out t) := rfl

theorem snd_inr (c : Copy p out) : snd p out (.inr c) = .inr c := rfl

theorem fanout_eq_one_of_not_two_le (t : Slot p out)
    (h : ¬ 2 ≤ fanout p out (slotSignal p out t)) : fanout p out (slotSignal p out t) = 1 := by
  have := fanout_pos_of_slot p out t
  omega

/-- The first endpoint of an edge belongs to the tree of its signal. -/
theorem signal_eq_of_fst_eq_inl {e : Edge p out} {w : Signal p out}
    (h : fst p out e = .inl w) : signal p out e = w := by
  rcases e with t | ⟨w', k⟩
  · by_cases h₂ : 2 ≤ fanout p out (slotSignal p out t)
    · rw [fst_inl_of_two_le p out t h₂] at h
      exact absurd h (by simp)
    · rw [fst_inl_of_fanout_eq_one p out t (fanout_eq_one_of_not_two_le p out t h₂)] at h
      simpa [signal] using h
  · by_cases h₀ : k.val = 0
    · simp only [fst, h₀, dite_true, Sum.inl.injEq] at h
      simpa [signal] using h
    · simp [fst, h₀] at h

theorem signal_eq_of_fst_eq_inr {e : Edge p out} {w : Signal p out}
    {k : Fin (fanout p out w - 1)} (h : fst p out e = .inr ⟨w, k⟩) : signal p out e = w := by
  rcases e with t | ⟨w', k'⟩
  · by_cases h₂ : 2 ≤ fanout p out (slotSignal p out t)
    · rw [fst_inl_of_two_le p out t h₂] at h
      simp only [Sum.inr.injEq, Sigma.mk.inj_iff] at h
      simpa [signal] using h.1
    · rw [fst_inl_of_fanout_eq_one p out t (fanout_eq_one_of_not_two_le p out t h₂)] at h
      exact absurd h (by simp)
  · by_cases h₀ : k'.val = 0
    · simp [fst, h₀] at h
    · simp only [fst, h₀, dite_false, Sum.inr.injEq, Sigma.mk.inj_iff] at h
      simpa [signal] using h.1

theorem signal_firstOut (w : Signal p out) (h : 0 < fanout p out w) :
    signal p out (firstOut p out w) = w := by
  unfold firstOut
  split_ifs with h₂
  · rfl
  · exact (mem_slots p out).mp ((slots p out w).equivFin.symm ⟨0, h⟩).2

theorem fst_firstOut (w : Signal p out) (h : 0 < fanout p out w) :
    fst p out (firstOut p out w) = .inl w := by
  unfold firstOut
  split_ifs with h₂
  · exact fst_inr_zero p out w _
  · have hs := (mem_slots p out).mp ((slots p out w).equivFin.symm ⟨0, h⟩).2
    rw [fst_inl_of_fanout_eq_one p out _ (by rw [hs]; omega), hs]

/-- The only edge leaving a signal vertex is its first outgoing edge. -/
theorem eq_firstOut_of_fst_eq_inl {e : Edge p out} {w : Signal p out}
    (h : fst p out e = .inl w) : e = firstOut p out w := by
  rcases e with t | ⟨w', k⟩
  · have hsig : slotSignal p out t = w := signal_eq_of_fst_eq_inl p out h
    by_cases h₂ : 2 ≤ fanout p out (slotSignal p out t)
    · rw [fst_inl_of_two_le p out t h₂] at h
      exact absurd h (by simp)
    · have hone : fanout p out w = 1 := by
        rw [← hsig]
        exact fanout_eq_one_of_not_two_le p out t h₂
      have hnot : ¬ 2 ≤ fanout p out w := by omega
      have hpos : 0 < fanout p out w := by omega
      simp only [firstOut, hnot, hpos, ↓reduceDIte]
      have h₁ : t ∈ slots p out w := (mem_slots p out).mpr hsig
      have h₃ := ((slots p out w).equivFin.symm ⟨0, hpos⟩).2
      rw [Finset.card_le_one.mp (le_of_eq hone) t h₁ _ h₃]
  · by_cases h₀ : k.val = 0
    · simp only [fst, h₀, dite_true, Sum.inl.injEq] at h
      subst h
      have h₂ : 2 ≤ fanout p out w' := by have := k.isLt; omega
      simp only [firstOut, h₂, ↓reduceDIte]
      congr 2
      exact Fin.ext h₀
    · simp [fst, h₀] at h

theorem input_ne_gate (j : Fin n) (g : Fin s) : Wire.input j ≠ (Wire.gate g : Wire n s) := by
  intro h
  have := congrArg Fin.val h
  simp only [Wire.input, Wire.gate, Fin.val_castAdd, Fin.val_natAdd] at this
  omega

/-- Every reachable wire other than the output gate feeds a slot. -/
theorem fanout_pos (w : Signal p out) (hne : w.1 ≠ Wire.gate out) : 0 < fanout p out w := by
  obtain ⟨w, hw⟩ := w
  cases hw with
  | out => exact absurd rfl hne
  | arg a hg => exact fanout_pos_of_slot p out ⟨(_, a), hg⟩

/-- The value a gate's operation takes on the bits of its two slots. -/
def opValue (g : Fin s) (h : Reach p out (Wire.gate g)) (α : Edge p out → Bool) : Bool :=
  (p.lines g).op (α (.inl ⟨(g, 0), h⟩)) (α (.inl ⟨(g, 1), h⟩))

/-- The local check of a vertex. A reachable gate requires its outgoing edge,
if any, to carry its operation applied to its slot bits, the output gate
requires that value to be `1`, and a copy vertex requires all its outgoing
edges to carry the bit of its incoming edge. Input vertices have no check. -/
def Check : Vertex p out → (Edge p out → Bool) → Prop
  | .inl w, α => ∀ (g : Fin s) (h : Reach p out (Wire.gate g)), w.1 = Wire.gate g →
      (0 < fanout p out w → α (firstOut p out w) = opValue p out g h α) ∧
        (g = out → opValue p out g h α = true)
  | .inr c, α => ∀ e, fst p out e = .inr c → α e = α (.inr c)

/-- The variables read by the circuit: the reachable input wires. -/
noncomputable def read : Finset (Fin n) :=
  Finset.univ.filter fun j => Reach p out (Wire.input j)

theorem mem_read {j : Fin n} : j ∈ read p out ↔ Reach p out (Wire.input j) := by
  simp [read]

/-- The vertex of an input variable. -/
noncomputable def portVertex (j : Fin n) : Vertex p out :=
  if h : Reach p out (Wire.input j) then .inl ⟨Wire.input j, h⟩ else .inl ⟨Wire.gate out, Reach.out⟩

/-- The edge carrying an input variable. -/
noncomputable def portEdge (j : Fin n) : Edge p out :=
  if h : Reach p out (Wire.input j) then firstOut p out ⟨Wire.input j, h⟩
  else .inl ⟨(out, 0), Reach.out⟩

theorem portVertex_of_reach {j : Fin n} (h : Reach p out (Wire.input j)) :
    portVertex p out j = .inl ⟨Wire.input j, h⟩ := by
  simp [portVertex, h]

theorem portEdge_of_reach {j : Fin n} (h : Reach p out (Wire.input j)) :
    portEdge p out j = firstOut p out ⟨Wire.input j, h⟩ := by
  simp [portEdge, h]

/-- The wiring graph as a constraint network. -/
noncomputable def network : Network n (Vertex p out) (Edge p out) where
  fst := fst p out
  snd := snd p out
  Check := Check p out
  check_local := by
    rintro (w | c) α β agree check
    · intro g h hw
      obtain ⟨hout, hfinal⟩ := check g h hw
      have slotEq : ∀ a : Fin 2, α (.inl ⟨(g, a), h⟩) = β (.inl ⟨(g, a), h⟩) := by
        intro a
        apply agree
        right
        rw [snd_inl]
        congr 1
        exact Subtype.ext hw.symm
      have opEq : opValue p out g h α = opValue p out g h β := by
        unfold opValue
        rw [slotEq 0, slotEq 1]
      refine ⟨fun hpos => ?_, fun hg => opEq ▸ hfinal hg⟩
      rw [← agree _ (Or.inl (fst_firstOut p out w hpos)), hout hpos, opEq]
    · intro e he
      rw [← agree e (Or.inl he), ← agree (.inr c) (Or.inr (snd_inr p out c))]
      exact check e he
  read := read p out
  portVertex := portVertex p out
  portEdge := portEdge p out
  port_incident := by
    intro j hj
    have h := (mem_read p out).mp hj
    rw [portVertex_of_reach p out h, portEdge_of_reach p out h]
    exact Or.inl (fst_firstOut p out _ (fanout_pos p out _ (input_ne_gate j out)))


/-! ## Semantics -/

/-- The value of a gate is its operation applied to the values of its argument wires. -/
theorem eval_eq_op (x : Fin n → Bool) (g : Fin s) :
    p.eval Binary.interpretation x g =
      (p.lines g).op (p.trace Binary.interpretation x ((p.lines g).wires 0))
        (p.trace Binary.interpretation x ((p.lines g).wires 1)) := by
  rw [← Program.lines_eval p Binary.interpretation x g]
  rfl

/-- The bits carried by the edges under the circuit's own evaluation. -/
noncomputable def traceAssignment (x : Fin n → Bool) : Edge p out → Bool :=
  fun e => p.trace Binary.interpretation x (signal p out e).1

theorem opValue_traceAssignment (x : Fin n → Bool) (g : Fin s) (h : Reach p out (Wire.gate g)) :
    opValue p out g h (traceAssignment p out x) = p.eval Binary.interpretation x g := by
  rw [eval_eq_op]
  rfl

/-- The evaluation of an accepted input satisfies every check and every port. -/
theorem traceAssignment_satisfies (x : Fin n → Bool)
    (hx : p.eval Binary.interpretation x out = true) :
    (network p out).Satisfies x (traceAssignment p out x) := by
  refine ⟨?_, ?_⟩
  · rintro (w | ⟨w, k⟩)
    · intro g h hw
      refine ⟨fun hpos => ?_, fun hg => ?_⟩
      · show traceAssignment p out x (firstOut p out w) = _
        rw [opValue_traceAssignment, traceAssignment, signal_firstOut p out w hpos, hw]
        simp
      · rw [opValue_traceAssignment, hg, hx]
    · intro e he
      show traceAssignment p out x e = traceAssignment p out x (.inr ⟨w, k⟩)
      unfold traceAssignment
      rw [signal_eq_of_fst_eq_inr p out he]
      rfl
  · intro j hj
    have h := (mem_read p out).mp hj
    show traceAssignment p out x (portEdge p out j) = x j
    rw [portEdge_of_reach p out h, traceAssignment,
      signal_firstOut p out _ (fanout_pos p out _ (input_ne_gate j out))]
    simp

/-- Under a satisfying assignment, the incoming edge of every copy vertex of a
signal carries the bit of the signal's first outgoing edge. -/
theorem copy_eq_firstOut_of_satisfies {x : Fin n → Bool} {α : Edge p out → Bool}
    (hα : (network p out).Satisfies x α) (w : Signal p out) (m : Nat)
    (hm : m < fanout p out w - 1) :
    α (.inr ⟨w, ⟨m, hm⟩⟩) = α (firstOut p out w) := by
  induction m with
  | zero =>
    have h₂ : 2 ≤ fanout p out w := by omega
    simp only [firstOut, h₂, ↓reduceDIte]
  | succ m ih =>
    have check := hα.1 (.inr ⟨w, ⟨m, by omega⟩⟩)
    rw [← ih (by omega)]
    exact check _ (fst_inr_succ p out w m hm)

/-- Under a satisfying assignment, every edge carrying a signal with positive
fan-out carries the bit of the signal's first outgoing edge. -/
theorem eq_firstOut_of_satisfies {x : Fin n → Bool} {α : Edge p out → Bool}
    (hα : (network p out).Satisfies x α) (w : Signal p out) (e : Edge p out)
    (he : signal p out e = w) : α e = α (firstOut p out w) := by
  rcases e with t | ⟨w', k⟩
  · have hw : slotSignal p out t = w := he
    by_cases h₂ : 2 ≤ fanout p out (slotSignal p out t)
    · have check := hα.1 (.inr ⟨slotSignal p out t, ⟨copyIndex p out t, copyIndex_lt p out t h₂⟩⟩)
      rw [check (.inl t) (fst_inl_of_two_le p out t h₂), ← hw]
      exact copy_eq_firstOut_of_satisfies p out hα _ _ _
    · apply congrArg α
      apply eq_firstOut_of_fst_eq_inl
      rw [fst_inl_of_fanout_eq_one p out t (fanout_eq_one_of_not_two_le p out t h₂), hw]
  · have hw : w' = w := he
    subst hw
    exact copy_eq_firstOut_of_satisfies p out hα w' k.val k.isLt

/-- Under a satisfying assignment, every edge carries the circuit's value of its signal. -/
theorem eq_trace_of_satisfies {x : Fin n → Bool} {α : Edge p out → Bool}
    (hα : (network p out).Satisfies x α) :
    ∀ (w : Signal p out) (e : Edge p out), signal p out e = w →
      α e = p.trace Binary.interpretation x w.1 := by
  suffices key : ∀ m, ∀ w : Signal p out, w.1.val = m → ∀ e, signal p out e = w →
      α e = p.trace Binary.interpretation x w.1 from fun w e he => key _ w rfl e he
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro w hm e he
  have hpos : 0 < fanout p out w := by
    rcases e with t | ⟨w', k⟩
    · have := fanout_pos_of_slot p out t
      rwa [show slotSignal p out t = w from he] at this
    · have hw : w' = w := he
      subst hw
      have := k.isLt
      omega
  rw [eq_firstOut_of_satisfies p out hα w e he]
  clear he
  obtain ⟨w, hw⟩ := w
  revert hw hm hpos
  refine Fin.addCases (fun j => ?_) (fun g => ?_) w
  · intro hw hm hpos
    have hj : j ∈ (network p out).read := (mem_read p out).mpr hw
    have := hα.2 j hj
    change α (portEdge p out j) = x j at this
    rw [portEdge_of_reach p out hw] at this
    rw [this]
    simp
  · intro hw hm hpos
    have check := (hα.1 (.inl ⟨Wire.gate g, hw⟩) g hw rfl).1 hpos
    rw [check, opValue]
    simp only [Program.trace_gateWire, Program.gateFunction_apply]
    rw [eval_eq_op]
    have slot (a : Fin 2) : α (.inl ⟨(g, a), hw⟩) =
        p.trace Binary.interpretation x ((p.lines g).wires a) := by
      refine ih _ ?_ (slotSignal p out ⟨(g, a), hw⟩) rfl (.inl ⟨(g, a), hw⟩) rfl
      rw [← hm]
      exact lines_wires_lt p g a
    rw [slot 0, slot 1]

/-- A satisfying assignment exists only for accepted inputs. -/
theorem eval_out_eq_true_of_satisfies {x : Fin n → Bool} {α : Edge p out → Bool}
    (hα : (network p out).Satisfies x α) : p.eval Binary.interpretation x out = true := by
  have check := (hα.1 (.inl ⟨Wire.gate out, Reach.out⟩) out Reach.out rfl).2 rfl
  rw [opValue, eq_trace_of_satisfies p out hα (slotSignal p out ⟨(out, 0), Reach.out⟩) _ rfl,
    eq_trace_of_satisfies p out hα (slotSignal p out ⟨(out, 1), Reach.out⟩) _ rfl] at check
  rw [eval_eq_op]
  exact check

/-- The wiring network accepts exactly the inputs accepted by the circuit. -/
theorem network_computes :
    (network p out).Computes fun x => p.eval Binary.interpretation x out := by
  intro x
  constructor
  · intro hx
    exact ⟨_, traceAssignment_satisfies p out x hx⟩
  · rintro ⟨α, hα⟩
    exact eval_out_eq_true_of_satisfies p out hα

/-! ## Graph properties -/

/-- No edge joins a vertex to itself. -/
theorem loopless : (network p out).Loopless := by
  rintro (t | ⟨w, k⟩)
  · show fst p out (.inl t) ≠ snd p out (.inl t)
    by_cases h₂ : 2 ≤ fanout p out (slotSignal p out t)
    · rw [fst_inl_of_two_le p out t h₂]
      simp [snd]
    · rw [fst_inl_of_fanout_eq_one p out t (fanout_eq_one_of_not_two_le p out t h₂)]
      simp only [snd, ne_eq, Sum.inl.injEq]
      intro h
      have := congrArg (fun w : Signal p out => w.1.val) h
      simp only [slotSignal, slotGate, Wire.gate, Fin.val_natAdd] at this
      have := lines_wires_lt p t.1.1 t.1.2
      omega
  · show fst p out (.inr ⟨w, k⟩) ≠ snd p out (.inr ⟨w, k⟩)
    by_cases h₀ : k.val = 0
    · simp [fst, snd, h₀]
    · simp only [fst, snd, h₀, ↓reduceDIte, ne_eq, Sum.inr.injEq]
      intro h
      have := congrArg (fun c : Copy p out => c.2.val) h
      simp only at this
      omega

/-- The edges leaving a vertex. -/
noncomputable def outEdges (v : Vertex p out) : Finset (Edge p out) :=
  Finset.univ.filter fun e => fst p out e = v

/-- The edges entering a vertex. -/
noncomputable def inEdges (v : Vertex p out) : Finset (Edge p out) :=
  Finset.univ.filter fun e => snd p out e = v

theorem mem_outEdges {v : Vertex p out} {e : Edge p out} :
    e ∈ outEdges p out v ↔ fst p out e = v := by
  simp [outEdges]

theorem mem_inEdges {v : Vertex p out} {e : Edge p out} :
    e ∈ inEdges p out v ↔ snd p out e = v := by
  simp [inEdges]

theorem edgesAt_subset (v : Vertex p out) :
    (network p out).edgesAt v ⊆ outEdges p out v ∪ inEdges p out v := by
  intro e he
  rcases (Multigraph.mem_edgesAt _).mp he with h | h
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)

theorem gate_injective {g g' : Fin s} (h : (Wire.gate g : Wire n s) = Wire.gate g') : g = g' := by
  have := congrArg Fin.val h
  simp only [Wire.gate, Fin.val_natAdd] at this
  exact Fin.ext (by omega)

/-- A signal vertex receives at most two edges: the slots of its gate. -/
theorem card_inEdges_inl_le (w : Signal p out) : (inEdges p out (.inl w)).card ≤ 2 := by
  let φ : Edge p out → Fin 2 := fun e => match e with
    | .inl t => t.1.2
    | .inr _ => 0
  have maps : Set.MapsTo φ ↑(inEdges p out (.inl w)) ↑(Finset.univ : Finset (Fin 2)) :=
    fun _ _ => Finset.mem_univ _
  have inj : Set.InjOn φ ↑(inEdges p out (.inl w)) := by
    rintro (t | c) ht (t' | c') ht' heq
    · have h1 : slotGate p out t = w :=
        Sum.inl.inj ((mem_inEdges p out).mp (Finset.mem_coe.mp ht))
      have h2 : slotGate p out t' = w :=
        Sum.inl.inj ((mem_inEdges p out).mp (Finset.mem_coe.mp ht'))
      have hgate : t.1.1 = t'.1.1 :=
        gate_injective (Subtype.ext_iff.mp (h1.trans h2.symm))
      have hslot : t.1.2 = t'.1.2 := heq
      congr 1
      exact Subtype.ext (Prod.ext hgate hslot)
    · exact absurd ((mem_inEdges p out).mp (Finset.mem_coe.mp ht')) (by simp [snd])
    · exact absurd ((mem_inEdges p out).mp (Finset.mem_coe.mp ht)) (by simp [snd])
    · exact absurd ((mem_inEdges p out).mp (Finset.mem_coe.mp ht)) (by simp [snd])
  simpa using Finset.card_le_card_of_injOn φ maps inj

/-- At most one edge leaves a signal vertex: its first outgoing edge. -/
theorem card_outEdges_inl_le (w : Signal p out) : (outEdges p out (.inl w)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro e he e' he'
  rw [eq_firstOut_of_fst_eq_inl p out ((mem_outEdges p out).mp he),
    eq_firstOut_of_fst_eq_inl p out ((mem_outEdges p out).mp he')]

/-- Exactly one edge enters a copy vertex. -/
theorem card_inEdges_inr_le (c : Copy p out) : (inEdges p out (.inr c)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  rintro (t | c') he (t' | c'') he'
  · exact absurd ((mem_inEdges p out).mp he) (by simp [snd])
  · exact absurd ((mem_inEdges p out).mp he) (by simp [snd])
  · exact absurd ((mem_inEdges p out).mp he') (by simp [snd])
  · have h1 : c' = c := Sum.inr.inj ((mem_inEdges p out).mp he)
    have h2 : c'' = c := Sum.inr.inj ((mem_inEdges p out).mp he')
    rw [h1, h2]

/-- A slot attached to a copy vertex has its position at least the copy's. -/
theorem copyIndex_le_slotIndex (t : Slot p out) : copyIndex p out t ≤ slotIndex p out t :=
  Nat.min_le_left _ _

/-- At most two edges leave a copy vertex: the next copy edge and its slots. -/
theorem card_outEdges_inr_le (w : Signal p out) (k : Fin (fanout p out w - 1)) :
    (outEdges p out (.inr ⟨w, k⟩)).card ≤ 2 := by
  -- Membership facts for the two kinds of edges.
  have slotMem : ∀ t : Slot p out, .inl t ∈ outEdges p out (.inr ⟨w, k⟩) →
      slotSignal p out t = w ∧ 2 ≤ fanout p out w ∧ copyIndex p out t = k.val := by
    intro t ht
    have h := (mem_outEdges p out).mp ht
    by_cases h₂ : 2 ≤ fanout p out (slotSignal p out t)
    · rw [fst_inl_of_two_le p out t h₂] at h
      simp only [Sum.inr.injEq, Sigma.mk.inj_iff] at h
      obtain ⟨hw, hk⟩ := h
      subst hw
      exact ⟨rfl, h₂, Fin.ext_iff.mp (eq_of_heq hk)⟩
    · rw [fst_inl_of_fanout_eq_one p out t (fanout_eq_one_of_not_two_le p out t h₂)] at h
      exact absurd h (by simp)
  have copyMem : ∀ (w' : Signal p out) (k' : Fin (fanout p out w' - 1)),
      .inr ⟨w', k'⟩ ∈ outEdges p out (.inr ⟨w, k⟩) → w' = w ∧ k'.val = k.val + 1 := by
    intro w' k' h
    have h := (mem_outEdges p out).mp h
    by_cases h₀ : k'.val = 0
    · simp [fst, h₀] at h
    · simp only [fst, h₀, ↓reduceDIte, Sum.inr.injEq, Sigma.mk.inj_iff] at h
      obtain ⟨hw, hk⟩ := h
      subst hw
      have := Fin.ext_iff.mp (eq_of_heq hk)
      simp only at this
      exact ⟨rfl, by omega⟩
  let φ : Edge p out → Nat := fun e => match e with
    | .inl t => slotIndex p out t - k.val
    | .inr _ => 1
  have maps : Set.MapsTo φ ↑(outEdges p out (.inr ⟨w, k⟩)) ↑(Finset.range 2) := by
    rintro (t | ⟨w', k'⟩) he
    · obtain ⟨hw, h₂, hk⟩ := slotMem t (Finset.mem_coe.mp he)
      have hlt := slotIndex_lt p out t
      rw [hw] at hlt
      have hmin : min (slotIndex p out t) (fanout p out w - 2) = k.val := by
        rw [← hk, copyIndex, hw]
      simp only [Finset.coe_range, Set.mem_Iio, φ]
      omega
    · simp [φ]
  have inj : Set.InjOn φ ↑(outEdges p out (.inr ⟨w, k⟩)) := by
    rintro (t | ⟨w', k'⟩) he (t' | ⟨w'', k''⟩) he' heq
    · obtain ⟨hw, h₂, hk⟩ := slotMem t (Finset.mem_coe.mp he)
      obtain ⟨hw', _, hk'⟩ := slotMem t' (Finset.mem_coe.mp he')
      have hle := copyIndex_le_slotIndex p out t
      have hle' := copyIndex_le_slotIndex p out t'
      have : slotIndex p out t = slotIndex p out t' := by
        simp only [φ] at heq
        omega
      rw [slotIndex_injective p out (hw.trans hw'.symm) this]
    · obtain ⟨hw, h₂, hk⟩ := slotMem t (Finset.mem_coe.mp he)
      obtain ⟨hw'', hk''⟩ := copyMem w'' k'' (Finset.mem_coe.mp he')
      subst hw''
      have hlt := k''.isLt
      have hle := copyIndex_le_slotIndex p out t
      have hmin : min (slotIndex p out t) (fanout p out w'' - 2) = k.val := by
        rw [← hk, copyIndex, hw]
      simp only [φ] at heq
      omega
    · obtain ⟨hw, hk⟩ := copyMem w' k' (Finset.mem_coe.mp he)
      obtain ⟨hw', h₂, hk'⟩ := slotMem t' (Finset.mem_coe.mp he')
      subst hw
      have hlt := k'.isLt
      have hle := copyIndex_le_slotIndex p out t'
      have hmin : min (slotIndex p out t') (fanout p out w' - 2) = k.val := by
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
theorem maxDegreeLE_three : (network p out).MaxDegreeLE 3 := by
  intro v
  refine (Finset.card_le_card (edgesAt_subset p out v)).trans
    ((Finset.card_union_le _ _).trans ?_)
  rcases v with w | ⟨w, k⟩
  · exact add_le_add (card_outEdges_inl_le p out w) (card_inEdges_inl_le p out w)
  · exact add_le_add (card_outEdges_inr_le p out w k) (card_inEdges_inr_le p out ⟨w, k⟩)

/-- The output gate's vertex. -/
def root : Vertex p out := .inl ⟨Wire.gate out, Reach.out⟩

theorem adj_of_edge (e : Edge p out) :
    (network p out).Adj (fst p out e) (snd p out e) :=
  ⟨e, Or.inl ⟨rfl, rfl⟩⟩

/-- Every copy vertex is joined to its signal vertex along the copy chain. -/
theorem copy_reaches_signal (w : Signal p out) (m : Nat) (hm : m < fanout p out w - 1) :
    Relation.ReflTransGen (network p out).Adj (.inr ⟨w, ⟨m, hm⟩⟩) (.inl w) := by
  induction m with
  | zero =>
    apply Relation.ReflTransGen.single
    have := adj_of_edge p out (.inr ⟨w, ⟨0, hm⟩⟩)
    rw [fst_inr_zero, snd_inr] at this
    exact this.symm
  | succ m ih =>
    refine Relation.ReflTransGen.head ?_ (ih (by omega))
    have := adj_of_edge p out (.inr ⟨w, ⟨m + 1, hm⟩⟩)
    rw [fst_inr_succ, snd_inr] at this
    exact this.symm

/-- Every reachable wire is joined to the output gate. -/
theorem signal_reaches_root : ∀ (w : Wire n s) (h : Reach p out w),
    Relation.ReflTransGen (network p out).Adj (.inl ⟨w, h⟩) (root p out) := by
  intro w h
  induction h with
  | out => exact Relation.ReflTransGen.refl
  | @arg g a hg ih =>
    let t : Slot p out := ⟨(g, a), hg⟩
    have toFst : Relation.ReflTransGen (network p out).Adj
        (.inl (slotSignal p out t)) (fst p out (.inl t)) := by
      by_cases h₂ : 2 ≤ fanout p out (slotSignal p out t)
      · rw [fst_inl_of_two_le p out t h₂]
        exact Multigraph.reflTransGen_adj_symm (copy_reaches_signal p out _ _ _)
      · rw [fst_inl_of_fanout_eq_one p out t (fanout_eq_one_of_not_two_le p out t h₂)]
    exact (toFst.tail (adj_of_edge p out (.inl t))).trans ih

/-- The wiring graph is connected. -/
theorem connected : (network p out).Connected := by
  apply Multigraph.connected_of_forall_reflTransGen (root p out)
  rintro (⟨w, h⟩ | ⟨w, k⟩)
  · exact signal_reaches_root p out w h
  · exact (copy_reaches_signal p out w k.val k.isLt).trans (signal_reaches_root p out w.1 w.2)

instance : Nonempty (Vertex p out) := ⟨root p out⟩

/-! ## Counting vertices and edges -/

/-- The reachable gates. -/
abbrev ReachableGate := {g : Fin s // Reach p out (Wire.gate g)}

/-- Edges plus signals equal vertices plus slots: both sides count every copy once. -/
theorem card_edge_add_card_signal :
    Fintype.card (Edge p out) + Fintype.card (Signal p out) =
      Fintype.card (Vertex p out) + Fintype.card (Slot p out) := by
  simp only [Fintype.card_sum]
  omega

/-- Every reachable gate has two slots. -/
theorem card_slot : Fintype.card (Slot p out) = 2 * Fintype.card (ReachableGate p out) := by
  let e : Slot p out ≃ ReachableGate p out × Fin 2 :=
    { toFun := fun t => (⟨t.1.1, t.2⟩, t.1.2)
      invFun := fun ga => ⟨(ga.1.1, ga.2), ga.1.2⟩
      left_inv := fun t => rfl
      right_inv := fun ga => rfl }
  rw [Fintype.card_congr e, Fintype.card_prod, Fintype.card_fin, mul_comm]

/-- The signals are the reachable inputs and the reachable gates. -/
theorem card_signal :
    Fintype.card (Signal p out) = (read p out).card + Fintype.card (ReachableGate p out) := by
  rw [Fintype.card_subtype, Fintype.card_subtype, read, Finset.card_filter, Finset.card_filter,
    Finset.card_filter, Fin.sum_univ_add]

/-- There are fewer copy vertices than slots. -/
theorem card_copy_le : Fintype.card (Copy p out) ≤ Fintype.card (Slot p out) := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  calc ∑ w : Signal p out, (fanout p out w - 1)
      ≤ ∑ w : Signal p out, fanout p out w := Finset.sum_le_sum fun w _ => Nat.sub_le _ _
    _ = Fintype.card (Slot p out) := by
      rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise
        (f := slotSignal p out) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
      rfl

theorem card_reachableGate_le : Fintype.card (ReachableGate p out) ≤ s := by
  simpa using Fintype.card_subtype_le fun g : Fin s => Reach p out (Wire.gate g)

theorem card_read_le : (read p out).card ≤ n := by
  simpa using Finset.card_le_univ (read p out)

/-- The vertex count is at most `n + 3 s`. -/
theorem card_vertex_le : Fintype.card (Vertex p out) ≤ n + 3 * s := by
  have h₁ := card_edge_add_card_signal p out
  have h₂ := card_slot p out
  have h₃ := card_signal p out
  have h₄ := card_copy_le p out
  have h₅ := card_reachableGate_le p out
  have h₆ := card_read_le p out
  simp only [Fintype.card_sum] at h₁ h₄ ⊢
  omega

/-- Edges minus vertices is reachable gates minus reachable inputs, as reals. -/
theorem card_edge_sub_card_vertex :
    (Fintype.card (Edge p out) : ℝ) - Fintype.card (Vertex p out) =
      (Fintype.card (ReachableGate p out) : ℝ) - (read p out).card := by
  have h₁ := card_edge_add_card_signal p out
  have h₂ := card_slot p out
  have h₃ := card_signal p out
  have h : (Fintype.card (Edge p out) : ℝ) + Fintype.card (Signal p out) =
      Fintype.card (Vertex p out) + Fintype.card (Slot p out) := by exact_mod_cast h₁
  have h' : (Fintype.card (Slot p out) : ℝ) = 2 * Fintype.card (ReachableGate p out) := by
    exact_mod_cast h₂
  have h'' : (Fintype.card (Signal p out) : ℝ) =
      (read p out).card + Fintype.card (ReachableGate p out) := by exact_mod_cast h₃
  linarith

end Wiring

end Cutwidth
end Algebraic
