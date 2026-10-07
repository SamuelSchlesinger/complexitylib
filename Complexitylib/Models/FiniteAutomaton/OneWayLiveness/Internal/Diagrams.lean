/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Models.FiniteAutomaton.OneWayLiveness.Internal.Network
public import Complexitylib.Models.FiniteAutomaton.OneWayLiveness.Internal.Diagram

/-!
# One-way-liveness proof: Diagrams

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Automata/Diagrams.lean

Module and namespace names, imports, and formatting are adapted to complexitylib.
The machine definitions are shared through `Models.FiniteAutomaton.Defs`.
-/

@[expose] public section

namespace Complexity.FiniteAutomaton
namespace Pairing
variable {A : Type} [Fintype A]

lemma prod_compatible_chain (as : List (Pairing (A ⊕ A))) (l r : A → Bool) :
    as.prod.Compatible (Sum.elim l r) ↔ ∃ b : ℕ → A → Bool,
      b 0 = l ∧ b as.length = r ∧
      ∀ i (hi : i < as.length), (as[i]).Compatible (Sum.elim (b i) (b (i+1))) := by
  induction as generalizing l with
  | nil =>
    change (identity A).Compatible (Sum.elim l r) ↔ _
    rw [identity_compatible]
    constructor
    · intro h; subst r; exact ⟨fun _ => l,rfl,rfl,by simp⟩
    · rintro ⟨b,hb,hb',_⟩; exact hb.symm.trans hb'
  | cons a as ih =>
    change (compose a as.prod).Compatible (Sum.elim l r) ↔ _
    rw [compose_compatible]
    constructor
    · rintro ⟨m,ha,has⟩
      obtain ⟨b,hb,hb',hc⟩ := (ih m).mp has
      refine ⟨fun i => Nat.casesOn i l b,rfl,hb',?_⟩
      intro i hi
      cases i with
      | zero => simpa [hb] using ha
      | succ i => exact hc i (by simpa using hi)
    · rintro ⟨b,hb,hb',hc⟩
      refine ⟨b 1, ?_, (ih (b 1)).mpr ⟨fun i => b (i+1),rfl,hb',?_⟩⟩
      · have hzero := hc 0 (by simp)
        change a.Compatible (Sum.elim (b 0) (b 1)) at hzero
        simpa only [hb] using hzero
      · intro i hi
        exact hc (i+1) (by simpa using hi)

lemma ofFn_compatible_chain {n : ℕ} (as : Fin n → Pairing (A ⊕ A)) (l r : A → Bool) :
    (List.ofFn as).prod.Compatible (Sum.elim l r) ↔ ∃ b : ℕ → A → Bool,
      b 0 = l ∧ b n = r ∧
      ∀ i : Fin n, (as i).Compatible (Sum.elim (b i.val) (b (i.val+1))) := by
  rw [prod_compatible_chain]
  simp only [List.length_ofFn, List.getElem_ofFn]
  constructor
  · rintro ⟨b,hl,hr,h⟩; exact ⟨b,hl,hr,fun i => h i.val i.isLt⟩
  · rintro ⟨b,hl,hr,h⟩; exact ⟨b,hl,hr,fun i hi => h ⟨i,hi⟩⟩
end Pairing

namespace CellNetwork
variable {Q Alpha : Type} [Fintype Q] (M : Machine Alpha Q)

/-- Boundary and tip colorings compatible with every local pairing and join. -/
structure ColorData (finish : Q) (w : List Alpha) where
  /-- Colors assigned to ports along each cell boundary. -/
  boundary : ℕ → Port Q → Bool
  /-- Colors assigned to the two tips of each cell incidence. -/
  tip : Fin (w.length + 2) → Tip Q → Bool
  port_eq : ∀ i s slot l, (if s then boundary (i.val+1) else boundary i.val) (slot,l) =
    tip i (.inl (s,slot),tipRole s l)
  stay_eq : ∀ i pq role t, tip i (.inr (pq,role),t) = tip i (.inr (pq,!role),!t)
  join_eq : ∀ i j, tip i (j,false) = tip i ((orders M finish (scanned w i)).perm j,true)

/-- The boundary pairing for one scanned symbol and chosen terminal state. -/
noncomputable def bodyDiagram (finish : Q) (b : Symbol Alpha) : Pairing (Port Q ⊕ Port Q) :=
  diagram Q (orders M finish b).perm

/-- The product of all cell diagrams, including the two endmarkers. -/
noncomputable def fullDiagram (finish : Q) (w : List Alpha) : Pairing (Port Q ⊕ Port Q) :=
  (List.ofFn fun i : Fin (w.length + 2) => bodyDiagram M finish (scanned w i)).prod

lemma fullDiagram_compatible (finish : Q) (w : List Alpha) (l r : Port Q → Bool) :
    (fullDiagram M finish w).Compatible (Sum.elim l r) ↔
      ∃ C : ColorData M finish w, C.boundary 0 = l ∧ C.boundary (w.length+2) = r := by
  classical
  rw [fullDiagram, Pairing.ofFn_compatible_chain]
  constructor
  · rintro ⟨b,hl,hr,hc⟩
    have hparts := fun i => (diagram_compatible Q (orders M finish (scanned w i)).perm
      (b i.val) (b (i.val+1))).mp (hc i)
    choose f hf using hparts
    exact ⟨⟨b,f,fun i => (hf i).1, fun i => (hf i).2.1,fun i => (hf i).2.2⟩,hl,hr⟩
  · rintro ⟨C,hl,hr⟩
    exact ⟨C.boundary,hl,hr,fun i => (diagram_compatible Q _ _ _).mpr
      ⟨C.tip i,C.port_eq i,C.stay_eq i,C.join_eq i⟩⟩

/-- Both lanes of every port slot have the same color. -/
def Flat (c : Port Q → Bool) : Prop := ∀ slot, c (slot,false) = c (slot,true)

/-- Flat boundary colors distinguish the initial and terminal test ports. -/
def Separated (finish : Q) (l r : Port Q → Bool) : Prop :=
  Flat l ∧ Flat r ∧ l (testSlot M finish,false) = false ∧ r (testSlot M finish,false) = true

namespace ColorData
variable {M} {finish : Q} {w : List Alpha} (C : ColorData M finish w)

/-- Restoring a reflection at every outer leaf extends the tip assignment. -/
def wholeTip : WholeInc Q w.length → Bool → Bool
  | .inl (i,j),t => C.tip i (j,t)
  | .inr (s,slot),t => C.boundary (if s then w.length+2 else 0) (slot,tipRole s (!t))

lemma wholeTip_join (hl : Flat (C.boundary 0)) (hr : Flat (C.boundary (w.length+2)))
    (x : WholeInc Q w.length) :
    C.wholeTip x false = C.wholeTip ((wholeOrder M finish w).perm x) true := by
  rcases x with ⟨i,j⟩ | ⟨s,slot⟩
  · exact C.join_eq i j
  · cases s with
    | false => exact (hl slot).symm
    | true => exact hr slot

lemma wholeTip_lane (d : Edge Q w.length × Bool) :
    C.wholeTip (edgeInc Q w.length d) true =
      C.wholeTip (edgeInc Q w.length ((graph M finish w).flip d)) false := by
  rcases d with ⟨(⟨j,⟨dir,p,q⟩⟩ | (⟨i,pq⟩ | ⟨s,slot⟩)),role⟩
  · have hleft (lane : Bool) := C.port_eq j.castSucc true (dir,p,q) lane
    have hright (lane : Bool) := C.port_eq j.succ false (dir,p,q) lane
    cases dir <;> cases role <;>
      simp only [edgeInc, FunctionalEdges.flip_apply, Bool.false_xor, Bool.true_xor,
        Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte, wholeTip] <;>
      first
        | exact (hleft false).symm.trans (hright false)
        | exact (hright true).symm.trans (hleft true)
  · exact C.stay_eq i pq role true
  · have hp (lane : Bool) := C.port_eq (outCell w.length s) s slot lane
    cases s <;> cases role <;>
      simp only [edgeInc, FunctionalEdges.flip_apply, Bool.not_false, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte, wholeTip, outCell, tipRole, Bool.false_xor,
        Bool.true_xor] <;>
      first
        | exact (hp false).symm
        | exact (hp true).symm
        | exact hp false
        | exact hp true

lemma tour_invariant (hl : Flat (C.boundary 0)) (hr : Flat (C.boundary (w.length+2)))
    (d : Edge Q w.length × Bool) :
    C.wholeTip (edgeInc Q w.length ((graphOrder M finish w).tour d)) true =
      C.wholeTip (edgeInc Q w.length d) true := by
  change C.wholeTip (edgeInc Q w.length ((graphOrder M finish w).perm
    ((graph M finish w).flip d))) true = _
  rw [graphOrder_apply, ← C.wholeTip_join hl hr]
  exact (C.wholeTip_lane d).symm

end ColorData
lemma reach_excludes_separation (finish : Q) (ht : M.transition finish .right = none)
    (w : List Alpha)
    (hp : Relation.ReflTransGen (M.Step w) (outCell w.length false,M.initial)
      (outCell w.length true,finish))
    (C : ColorData M finish w) : ¬ Separated M finish (C.boundary 0) (C.boundary (w.length+2)) := by
  rintro ⟨hl,hr,hleft,hright⟩
  let eL : Edge Q w.length := .inr (.inr (false,testSlot M finish))
  let eR : Edge Q w.length := .inr (.inr (true,testSlot M finish))
  have hterm : ∀ e, (graph M finish w).src e ≠
      stateVertex w (outCell w.length true,finish) :=
    graph_terminal M finish w _ (by simpa only [scanned_outCell, ↓reduceIte] using ht)
  have hL : (graph M finish w).Reach ((graph M finish w).vertex (eL,false))
      (stateVertex w (outCell w.length true,finish)) :=
    ((graph_reach_state M finish w _ _).mpr hp).head (test_step M finish w false)
  have hR : (graph M finish w).Reach ((graph M finish w).vertex (eR,false))
      (stateVertex w (outCell w.length true,finish)) :=
    Relation.ReflTransGen.single (test_step M finish w true)
  have hh := (graphOrder M finish w).basin_sameCycle hterm (eL,false) (eR,false) (eR,true)
    hL hR (test_destination M finish w true)
  have he := FunctionalEdges.Rotation.color_eq_of_sameCycle (graphOrder M finish w).tour
    (fun d => C.wholeTip (edgeInc Q w.length d) true) (C.tour_invariant hl hr) hh
  change C.boundary 0 (testSlot M finish,false) =
    C.boundary (w.length+2) (testSlot M finish,true) at he
  rw [hleft, ← hr _, hright] at he
  cases he

omit [Fintype Q] in
/-- A vertex coloring which is constant along all edges also respects
all local joins, regardless of cycles in other components. -/
lemma vertex_color_flip (finish : Q) (w : List Alpha) (c : Vertex Q w.length → Bool)
    (hc : ∀ e, c ((graph M finish w).src e) = c ((graph M finish w).dst e))
    (d : Edge Q w.length × Bool) :
    c (wholeVertex M finish w (edgeInc Q w.length d)) =
      c (wholeVertex M finish w (edgeInc Q w.length ((graph M finish w).flip d))) := by
  rw [← graph_vertex, ← graph_vertex]
  rcases d with ⟨e,b⟩
  cases b with
  | false => exact hc e
  | true => exact (hc e).symm

omit [Fintype Q] in
lemma vertex_color_adjacent (finish : Q) (w : List Alpha) (c : Vertex Q w.length → Bool)
    (hc : ∀ e, c ((graph M finish w).src e) = c ((graph M finish w).dst e))
    (i : Fin (w.length+1)) (slot : Slot Q) :
    c (wholeVertex M finish w (.inl (i.castSucc,.inl (true,slot)))) =
      c (wholeVertex M finish w (.inl (i.succ,.inl (false,slot)))) := by
  have h := vertex_color_flip M finish w c hc (.inl (i,slot),false)
  rcases slot with ⟨d,p,q⟩
  cases d with
  | false => exact h.symm
  | true => exact h

/-- Read a boundary-port color from the corresponding graph vertex. -/
noncomputable def boundaryColor (finish : Q) (w : List Alpha) (c : Vertex Q w.length → Bool)
    (k : ℕ) (p : Port Q) : Bool :=
  if hk : k = 0 then c (wholeVertex M finish w (.inl (⟨0,by omega⟩,.inl (false,p.1))))
  else if hk' : k-1 < w.length+2 then
    c (wholeVertex M finish w (.inl (⟨k-1,hk'⟩,.inl (true,p.1)))) else false

omit [Fintype Q] in
lemma boundaryColor_right (finish : Q) (w : List Alpha) (c : Vertex Q w.length → Bool)
    (i : Fin (w.length+2)) (slot : Slot Q) (lane : Bool) :
    boundaryColor M finish w c (i.val+1) (slot,lane) =
      c (wholeVertex M finish w (.inl (i,.inl (true,slot)))) := by
  simp [boundaryColor, i.isLt]

omit [Fintype Q] in
lemma boundaryColor_left (finish : Q) (w : List Alpha) (c : Vertex Q w.length → Bool)
    (hc : ∀ e, c ((graph M finish w).src e) = c ((graph M finish w).dst e))
    (i : Fin (w.length+2)) (slot : Slot Q) (lane : Bool) :
    boundaryColor M finish w c i.val (slot,lane) =
      c (wholeVertex M finish w (.inl (i,.inl (false,slot)))) := by
  by_cases hi : i.val = 0
  · have he : i = ⟨0,by omega⟩ := Fin.ext hi
    rw [he]
    simp [boundaryColor]
  · have hb : i.val-1 < w.length+2 := by omega
    rw [boundaryColor, dite_eq_right hi, dite_eq_left hb]
    let j : Fin (w.length+1) := ⟨i.val-1,by omega⟩
    have hj : j.succ = i := Fin.ext (by dsimp [j]; omega)
    exact (vertex_color_adjacent M finish w c hc j slot).trans (congrArg
      (fun k => c (wholeVertex M finish w (.inl (k,.inl (false,slot))))) hj)

/-- An edge-constant vertex coloring induces compatible local color data. -/
noncomputable def vertexColorData (finish : Q) (w : List Alpha) (c : Vertex Q w.length → Bool)
    (hc : ∀ e, c ((graph M finish w).src e) = c ((graph M finish w).dst e)) :
    ColorData M finish w where
  boundary := boundaryColor M finish w c
  tip i j := c (wholeVertex M finish w (.inl (i,j.1)))
  port_eq i s slot lane := by
    cases s with
    | false => exact boundaryColor_left M finish w c hc i slot lane
    | true => exact boundaryColor_right M finish w c i slot lane
  stay_eq i pq role t := vertex_color_flip M finish w c hc (.inr (.inl (i,pq)),role)
  join_eq i j :=
    congrArg (fun v => c (.inl (i,v))) ((orders M finish (scanned w i)).vertex_eq j).symm

omit [Fintype Q] in
lemma boundaryColor_test (finish : Q) (w : List Alpha) (c : Vertex Q w.length → Bool)
    (hc : ∀ e, c ((graph M finish w).src e) = c ((graph M finish w).dst e)) (s lane : Bool) :
    boundaryColor M finish w c (if s then w.length+2 else 0) (testSlot M finish,lane) =
      c (stateVertex w (outCell w.length s,if s then finish else M.initial)) := by
  calc
    _ = c (wholeVertex M finish w (.inl (outCell w.length s,.inl (s,testSlot M finish)))) := by
      cases s with
      | false => exact boundaryColor_left M finish w c hc (outCell w.length false) _ _
      | true => exact boundaryColor_right M finish w c (outCell w.length true) _ _
    _ = _ := congrArg c (test_destination M finish w s)

lemma separation_of_not_reach (finish : Q) (ht : M.transition finish .right = none)
    (w : List Alpha)
    (hp : ¬ Relation.ReflTransGen (M.Step w) (outCell w.length false,M.initial)
      (outCell w.length true,finish)) :
    ∃ C : ColorData M finish w, Separated M finish (C.boundary 0) (C.boundary (w.length+2)) := by
  classical
  let sink := stateVertex w (outCell w.length true,finish)
  have hterm : ∀ e, (graph M finish w).src e ≠ sink :=
    graph_terminal M finish w _ (by simpa only [scanned_outCell, ↓reduceIte] using ht)
  let c : Vertex Q w.length → Bool := fun v => decide ((graph M finish w).Reach v sink)
  have hc : ∀ e, c ((graph M finish w).src e) = c ((graph M finish w).dst e) := by
    intro e
    apply Bool.eq_iff_iff.mpr
    simp only [c, decide_eq_true_eq]
    exact ⟨fun h => (graph M finish w).successor_reaches hterm h ⟨e,rfl,rfl⟩,
      fun h => h.head ⟨e,rfl,rfl⟩⟩
  refine ⟨vertexColorData M finish w c hc, ?_, ?_, ?_, ?_⟩
  · intro slot; rfl
  · intro slot; rfl
  · change boundaryColor M finish w c 0 _ = false
    rw [show (0 : ℕ) = (if false then w.length+2 else 0) from rfl,
      boundaryColor_test M finish w c hc false false]
    change decide ((graph M finish w).Reach
      (stateVertex w (outCell w.length false,M.initial)) sink) = false
    rw [decide_eq_false_iff_not, graph_reach_state]
    exact hp
  · change boundaryColor M finish w c (w.length+2) _ = true
    rw [show w.length+2 = (if true then w.length+2 else 0) from rfl,
      boundaryColor_test M finish w c hc true false]
    change decide ((graph M finish w).Reach sink sink) = true
    exact decide_eq_true Relation.ReflTransGen.refl

/-- The Boolean test recovers exactly acceptance, not a halting assumption.
Only the normalized distinguished right state is required to be terminal. -/
lemma diagram_recognizes_reach (finish : Q) (ht : M.transition finish .right = none)
    (w : List Alpha) :
    (¬ ∃ l r, (fullDiagram M finish w).Compatible (Sum.elim l r) ∧ Separated M finish l r) ↔
      Relation.ReflTransGen (M.Step w) (outCell w.length false,M.initial)
        (outCell w.length true,finish) := by
  classical
  constructor
  · intro h
    by_contra hn
    obtain ⟨C,hC⟩ := separation_of_not_reach M finish ht w hn
    exact h ⟨C.boundary 0,C.boundary (w.length+2),
      (fullDiagram_compatible M finish w _ _).mpr ⟨C,rfl,rfl⟩,hC⟩
  · rintro h ⟨l,r,hd,hs⟩
    obtain ⟨C,rfl,rfl⟩ := (fullDiagram_compatible M finish w l r).mp hd
    exact reach_excludes_separation M finish ht w h C hs

end CellNetwork
end Complexity.FiniteAutomaton
