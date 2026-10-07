/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Models.FiniteAutomaton.OneWayLiveness.Internal.Cells
public import Complexitylib.Models.FiniteAutomaton.OneWayLiveness.Internal.Tours
public import Complexitylib.Models.FiniteAutomaton.OneWayLiveness.Internal.Normalization

/-!
# One-way-liveness proof: Network

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Automata/Network.lean

Module and namespace names, imports, and formatting are adapted to complexitylib.
The machine definitions are shared through `Models.FiniteAutomaton.Defs`.
-/

@[expose] public section

namespace Complexity.FiniteAutomaton
namespace CellNetwork
variable (Q : Type)

/-- Edges of all crossing and stay candidates, together with all outward
slots. Every outward slot is an edge to its own external leaf. -/
abbrev Edge (n : ℕ) := (Fin (n + 1) × Slot Q) ⊕
  ((Fin (n + 2) × (Q × Q)) ⊕ (Bool × Slot Q))
/-- All cell incidences, together with the external boundary incidences. -/
abbrev WholeInc (n : ℕ) := (Fin (n + 2) × Incidence Q) ⊕ (Bool × Slot Q)

/-- The left or right endmarker position. -/
def outCell (n : ℕ) (s : Bool) : Fin (n + 2) :=
  if s then ⟨n + 1, by omega⟩ else ⟨0, by omega⟩

/-- Locate an oriented incidence in its cell, or at its external leaf. -/
def edgeInc (n : ℕ) : Edge Q n × Bool → WholeInc Q n
  | (.inl (j,slot),b) =>
      if slot.1 ^^ b then .inl (j.castSucc, .inl (true,slot))
      else .inl (j.succ, .inl (false,slot))
  | (.inr (.inl (i,pq)),b) => .inl (i,.inr (pq,b))
  | (.inr (.inr (s,slot)),b) =>
      if b then .inl (outCell n s,.inl (s,slot)) else .inr (s,slot)

/-- Recover the edge and endpoint corresponding to an incidence. -/
def incEdge (n : ℕ) : WholeInc Q n → Edge Q n × Bool
  | .inl (i,.inl (false,slot)) =>
      if h : i.val = 0 then (.inr (.inr (false,slot)),true)
      else (.inl (⟨i.val - 1, by omega⟩,slot),slot.1)
  | .inl (i,.inl (true,slot)) =>
      if h : i.val = n + 1 then (.inr (.inr (true,slot)),true)
      else (.inl (⟨i.val, by omega⟩,slot),!slot.1)
  | .inl (i,.inr (pq,b)) => (.inr (.inl (i,pq)),b)
  | .inr (s,slot) => (.inr (.inr (s,slot)),false)

lemma incEdge_edgeInc (n : ℕ) (d : Edge Q n × Bool) : incEdge Q n (edgeInc Q n d) = d := by
  rcases d with ⟨(⟨j,⟨dir,p,q⟩⟩ | (⟨i,pq⟩ | ⟨s,slot⟩)),b⟩
  · have hj : j.val ≠ n + 1 := Nat.ne_of_lt j.isLt
    cases dir <;> cases b <;> simp [edgeInc, incEdge, hj]
  · rfl
  · cases s <;> cases b <;> simp [edgeInc, incEdge, outCell]

lemma edgeInc_incEdge (n : ℕ) (d : WholeInc Q n) : edgeInc Q n (incEdge Q n d) = d := by
  rcases d with ⟨i,(⟨s,⟨dir,p,q⟩⟩ | ⟨pq,b⟩)⟩ | ⟨s,slot⟩
  · cases s with
    | false =>
      simp only [incEdge]
      split_ifs with hi
      · have he : i = ⟨0,by omega⟩ := Fin.ext hi
        rw [he]
        rfl
      · cases dir <;> simp only [edgeInc, Bool.false_xor, Bool.true_xor, Bool.not_true,
          Bool.false_eq_true, ↓reduceIte]
        all_goals congr 2; apply Fin.ext; dsimp; omega
    | true =>
      simp only [incEdge]
      split_ifs with hi
      · have he : i = ⟨n+1,by omega⟩ := Fin.ext hi
        rw [he]
        rfl
      · cases dir <;> simp [edgeInc]
  · rfl
  · rfl

/-- Identify edge endpoints with the full set of incidences. -/
def incidenceEquiv (n : ℕ) : (Edge Q n × Bool) ≃ WholeInc Q n where
  toFun := edgeInc Q n
  invFun := incEdge Q n
  left_inv := incEdge_edgeInc Q n
  right_inv := edgeInc_incEdge Q n


/-- A complete proposed successor, including its source and target state. -/
abbrev Key := Move × Q × Q

/-- The incidence associated with the source of a potential transition. -/
def sourceInc : Key Q → Incidence Q
  | (.left,p,q) => .inl (false,(false,p,q))
  | (.stay,p,q) => .inr ((p,q),false)
  | (.right,p,q) => .inl (true,(true,p,q))

lemma sourceInc_injective : Function.Injective (sourceInc Q) := by
  rintro ⟨d,p,q⟩ ⟨d',p',q'⟩ h
  cases d <;> cases d' <;> simp_all [sourceInc]

variable {Q} {Alpha : Type} (M : Machine Alpha Q)

/-- Attach an enabled transition to its source state; otherwise leave it unattached. -/
noncomputable def sourceAttach (b : Symbol Alpha) (k : Key Q) : LocalVertex Q := by
  classical
  exact if M.transition k.2.1 b = some (k.2.2,k.1) then .inl k.2.1 else .inr (sourceInc Q k)

lemma sourceAttach_injective (b : Symbol Alpha) : Function.Injective (sourceAttach M b) := by
  classical
  rintro ⟨d,p,q⟩ ⟨d',p',q'⟩ h
  dsimp only [sourceAttach] at h
  split_ifs at h with hk hk'
  · have he : p = p' := Sum.inl.inj h
    subst p'
    have he := Option.some.inj (hk.symm.trans hk')
    have hq : q = q' := congrArg Prod.fst he
    cases hq
    have hd : d = d' := congrArg Prod.snd he
    cases hd
    rfl
  · exact sourceInc_injective Q (Sum.inr.inj h)

lemma sourceAttach_eq_state (b : Symbol Alpha) (k : Key Q) (p : Q) :
    sourceAttach M b k = .inl p ↔ k.2.1 = p ∧ M.transition p b = some (k.2.2,k.1) := by
  classical
  simp only [sourceAttach]
  split_ifs with hk
  · simp only [Sum.inl.injEq]
    constructor
    · intro h; exact ⟨h, h ▸ hk⟩
    · exact And.left
  · constructor
    · intro h; cases h
    · rintro ⟨h, hh⟩; exact (hk (h.symm ▸ hh)).elim

/-- Only the side facing away from the input is outward. -/
def outward : Symbol Alpha → Bool → Bool
  | .left, s => !s
  | .right, s => s
  | .letter _, _ => false

/-- The external test slot connecting the initial state to the selected final state. -/
def testSlot (finish : Q) : Slot Q := (true, M.initial, finish)

/-- Attach enabled transitions and designated test ports to their local states. -/
noncomputable def localVertex (finish : Q) (b : Symbol Alpha) : Incidence Q → LocalVertex Q := by
  classical
  exact fun i => match i with
    | .inl (s,slot) =>
      if outward b s then
        if slot = testSlot M finish then .inl (if s then finish else M.initial) else .inr i
      else if s = slot.1 then
        sourceAttach M b (if s then .right else .left,slot.2.1,slot.2.2)
      else .inl slot.2.2
    | .inr (pq,r) => if r then .inl pq.2 else sourceAttach M b (.stay,pq.1,pq.2)

variable (Q)
/-- An edge is uniquely determined by the cell, move and states of its
source proposal, or by its outward slot. -/
def edgeKey (n : ℕ) : Edge Q n → (Fin (n + 2) × Key Q) ⊕ (Bool × Slot Q)
  | .inl (j,(true,p,q)) => .inl (j.castSucc,(.right,p,q))
  | .inl (j,(false,p,q)) => .inl (j.succ,(.left,p,q))
  | .inr (.inl (i,(p,q))) => .inl (i,(.stay,p,q))
  | .inr (.inr z) => .inr z

lemma edgeKey_injective (n : ℕ) : Function.Injective (edgeKey Q n) := by
  rintro (⟨i,⟨d,p,q⟩⟩ | (⟨i,⟨p,q⟩⟩ | z)) (⟨j,⟨d',p',q'⟩⟩ | (⟨j,⟨p',q'⟩⟩ | z')) h
  all_goals first
    | (cases d <;> cases d' <;> simp_all [edgeKey])
    | (cases d <;> simp_all [edgeKey])
    | (cases d' <;> simp_all [edgeKey])
    | simp_all [edgeKey]

/-- Local vertices in each cell, together with the external test ports. -/
abbrev Vertex (n : ℕ) := (Fin (n + 2) × LocalVertex Q) ⊕ (Bool × Slot Q)
variable {Q}

/-- Map source keys and external incidences into the global vertex set. -/
noncomputable def decorate (w : List Alpha) :
    (Fin (w.length + 2) × Key Q) ⊕ (Bool × Slot Q) → Vertex Q w.length
  | .inl (i,k) => .inl (i,sourceAttach M (scanned w i) k)
  | .inr z => .inr z

lemma decorate_injective (w : List Alpha) : Function.Injective (decorate M w) := by
  rintro (⟨i,k⟩ | z) (⟨j,k'⟩ | z') h
  · have he := Sum.inl.inj h
    have hij : i = j := congrArg Prod.fst he
    subst j
    have hk := sourceAttach_injective M (scanned w i) (congrArg Prod.snd he)
    cases hk
    rfl
  · cases h
  · cases h
  · exact congrArg Sum.inr (Sum.inr.inj h)

/-- The target vertex of a transition or external boundary edge. -/
noncomputable def destination (finish : Q) (w : List Alpha) : Edge Q w.length → Vertex Q w.length
  | .inl (j,(true,_p,q)) => .inl (j.succ,.inl q)
  | .inl (j,(false,_p,q)) => .inl (j.castSucc,.inl q)
  | .inr (.inl (i,(_p,q))) => .inl (i,.inl q)
  | .inr (.inr (s,slot)) => .inl (outCell w.length s,
      localVertex M finish (scanned w (outCell w.length s)) (.inl (s,slot)))

/-- The functional graph encoding the machine run and its test ports. -/
noncomputable def graph (finish : Q) (w : List Alpha) :
    FunctionalEdges (Vertex Q w.length) (Edge Q w.length) where
  src e := decorate M w (edgeKey Q w.length e)
  dst := destination M finish w
  src_injective := (decorate_injective M w).comp (edgeKey_injective Q w.length)

/-- The graph vertex associated with each cell or boundary incidence. -/
noncomputable def wholeVertex (finish : Q) (w : List Alpha) :
    WholeInc Q w.length → Vertex Q w.length
  | .inl (i,j) => .inl (i,localVertex M finish (scanned w i) j)
  | .inr z => .inr z

lemma outward_internal (w : List Alpha) (j : Fin (w.length + 1)) :
    outward (scanned w j.castSucc) true = false ∧ outward (scanned w j.succ) false = false := by
  constructor
  · have hr : scanned w j.castSucc ≠ .right := by
      rw [ne_eq, scanned_eq_right_iff]; exact Nat.ne_of_lt j.isLt
    cases h : scanned w j.castSucc <;> simp_all [outward]
  · have hl : scanned w j.succ ≠ .left := by
      rw [ne_eq, scanned_eq_left_iff]; simp
    cases h : scanned w j.succ <;> simp_all [outward]

lemma graph_vertex (finish : Q) (w : List Alpha) (d : Edge Q w.length × Bool) :
    (graph M finish w).vertex d = wholeVertex M finish w (edgeInc Q w.length d) := by
  classical
  rcases d with ⟨(⟨j,⟨dir,p,q⟩⟩ | (⟨i,pq⟩ | ⟨s,slot⟩)),b⟩
  · obtain ⟨hl,hr⟩ := outward_internal w j
    cases dir <;> cases b <;>
      simp [FunctionalEdges.vertex, graph, decorate, edgeKey, destination, wholeVertex, edgeInc,
        localVertex, hl, hr]
  · cases b <;> rfl
  · cases b <;> rfl


/-- The same local cyclic orders are used at every occurrence of a symbol. -/
def wholePerm (w : List Alpha) (r : Symbol Alpha → Equiv.Perm (Incidence Q)) :
    Equiv.Perm (WholeInc Q w.length) where
  toFun x := match x with
    | .inl (i,j) => .inl (i,r (scanned w i) j)
    | .inr z => .inr z
  invFun x := match x with
    | .inl (i,j) => .inl (i,(r (scanned w i)).symm j)
    | .inr z => .inr z
  left_inv x := by cases x <;> simp
  right_inv x := by cases x <;> simp

lemma wholePerm_pow (w : List Alpha) (r : Symbol Alpha → Equiv.Perm (Incidence Q))
    (n : ℕ) (i : Fin (w.length + 2)) (j : Incidence Q) :
    (wholePerm w r ^ n) (.inl (i,j)) = .inl (i,(r (scanned w i) ^ n) j) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ', Equiv.Perm.mul_apply, ih]; rfl

/-- Choose a cyclic order for every local-vertex incidence fiber. -/
noncomputable def orders [Fintype Q] (finish : Q) (b : Symbol Alpha) :
    CyclicOrder (localVertex M finish b) := CyclicOrder.choose _

/-- Combine the local cyclic incidence orders over the whole input. -/
noncomputable def wholeOrder [Fintype Q] (finish : Q) (w : List Alpha) :
    CyclicOrder (wholeVertex M finish w) where
  perm := wholePerm w (fun b => (orders M finish b).perm)
  vertex_eq x := by
    rcases x with ⟨i,j⟩ | z
    · change Sum.inl (i,localVertex M finish _ ((orders M finish (scanned w i)).perm j)) = _
      rw [(orders M finish (scanned w i)).vertex_eq]
      rfl
    · rfl
  cyclic := by
    rintro (⟨i,j⟩ | z) (⟨i',j'⟩ | z') h
    · have he := Sum.inl.inj h
      have hi : i = i' := congrArg Prod.fst he
      subst i'
      have hj := congrArg Prod.snd he
      obtain ⟨n, hn⟩ := ((orders M finish (scanned w i)).cyclic j j' hj).exists_nat_pow_eq
      refine ⟨n, ?_⟩
      simp only [zpow_natCast, wholePerm_pow, hn]
    · cases h
    · cases h
    · have hz := Sum.inr.inj h
      exact (congrArg Sum.inr hz).sameCycle _

/-- Transport the incidence order to a rotation system on graph edge endpoints. -/
noncomputable def graphOrder [Fintype Q] (finish : Q) (w : List Alpha) :
    (graph M finish w).Rotation where
  perm := (incidenceEquiv Q w.length).symm.permCongrHom (wholeOrder M finish w).perm
  vertex_eq d := by
    rw [graph_vertex, graph_vertex]
    change wholeVertex M finish w (incidenceEquiv Q w.length
      ((incidenceEquiv Q w.length).symm
        ((wholeOrder M finish w).perm (incidenceEquiv Q w.length d)))) = _
    rw [Equiv.apply_symm_apply]
    exact (wholeOrder M finish w).vertex_eq _
  cyclic d d' h := by
    rw [graph_vertex, graph_vertex] at h
    have hh := (wholeOrder M finish w).cyclic _ _ h
    change (wholeOrder M finish w).perm.SameCycle (incidenceEquiv Q w.length d)
      (incidenceEquiv Q w.length d') at hh
    simpa only [Equiv.symm_apply_apply] using
      sameCycle_permCongr (incidenceEquiv Q w.length).symm (wholeOrder M finish w).perm hh

lemma graphOrder_apply [Fintype Q] (finish : Q) (w : List Alpha) (d : Edge Q w.length × Bool) :
    edgeInc Q w.length ((graphOrder M finish w).perm d) =
      (wholeOrder M finish w).perm (edgeInc Q w.length d) := by
  change incidenceEquiv Q w.length ((incidenceEquiv Q w.length).symm (_)) = _
  exact (incidenceEquiv Q w.length).apply_symm_apply _

/-- State configurations embed without identifying any added leaves. -/
def stateVertex (w : List Alpha) (c : Machine.Config (Q := Q) w) : Vertex Q w.length :=
  .inl (c.1,.inl c.2)

lemma stateVertex_injective (w : List Alpha) : Function.Injective (stateVertex (Q := Q) w) := by
  rintro ⟨i,p⟩ ⟨j,q⟩ h
  simpa [stateVertex] using h

lemma graph_step_from_state (finish : Q) (w : List Alpha) (c : Machine.Config (Q := Q) w)
    (v : Vertex Q w.length) :
    (graph M finish w).Step (stateVertex w c) v ↔
      ∃ c', v = stateVertex w c' ∧ M.Step w c c' := by
  classical
  constructor
  · rintro ⟨e, hs, hd⟩
    rcases c with ⟨i,p⟩
    rcases e with ⟨j,⟨dir,p',q⟩⟩ | (⟨j,⟨p',q⟩⟩ | z)
    · cases dir with
      | false =>
        change Sum.inl (j.succ,sourceAttach M (scanned w j.succ) (.left,p',q)) =
          Sum.inl (i,Sum.inl p) at hs
        have he := Sum.inl.inj hs
        have hi : j.succ = i := congrArg Prod.fst he
        subst i
        obtain ⟨hp, ht⟩ := (sourceAttach_eq_state M _ _ _).mp (congrArg Prod.snd he)
        exact ⟨(j.castSucc,q), hd.symm, .left, ht, rfl⟩
      | true =>
        change Sum.inl (j.castSucc,sourceAttach M (scanned w j.castSucc) (.right,p',q)) =
          Sum.inl (i,Sum.inl p) at hs
        have he := Sum.inl.inj hs
        have hi : j.castSucc = i := congrArg Prod.fst he
        subst i
        obtain ⟨hp, ht⟩ := (sourceAttach_eq_state M _ _ _).mp (congrArg Prod.snd he)
        exact ⟨(j.succ,q), hd.symm, .right, ht, rfl⟩
    · change Sum.inl (j,sourceAttach M (scanned w j) (.stay,p',q)) =
        Sum.inl (i,Sum.inl p) at hs
      have he := Sum.inl.inj hs
      have hi : j = i := congrArg Prod.fst he
      subst i
      obtain ⟨hp, ht⟩ := (sourceAttach_eq_state M _ _ _).mp (congrArg Prod.snd he)
      exact ⟨(j,q), hd.symm, .stay, ht, rfl⟩
    · cases hs
  · rintro ⟨⟨j,q⟩, rfl, d, ht, hr⟩
    rcases c with ⟨i,p⟩
    cases d with
    | left =>
      change j.val + 1 = i.val at hr
      let k : Fin (w.length + 1) := ⟨j.val, by omega⟩
      have hk : k.succ = i := Fin.ext hr
      refine ⟨.inl (k,(false,p,q)), ?_, ?_⟩
      · change Sum.inl (k.succ,sourceAttach M (scanned w k.succ) (.left,p,q)) = _
        rw [hk]
        rw [(sourceAttach_eq_state M _ _ _).mpr ⟨rfl, ht⟩]
        rfl
      · rfl
    | stay =>
      have hj : j = i := Fin.ext hr
      subst j
      refine ⟨.inr (.inl (i,(p,q))), ?_, rfl⟩
      change Sum.inl (i,sourceAttach M (scanned w i) (.stay,p,q)) = _
      rw [(sourceAttach_eq_state M _ _ _).mpr ⟨rfl, ht⟩]
      rfl
    | right =>
      change j.val = i.val + 1 at hr
      let k : Fin (w.length + 1) := ⟨i.val, by omega⟩
      have hk : k.succ = j := Fin.ext hr.symm
      refine ⟨.inl (k,(true,p,q)), ?_, ?_⟩
      · change Sum.inl (i,sourceAttach M (scanned w i) (.right,p,q)) = _
        rw [(sourceAttach_eq_state M _ _ _).mpr ⟨rfl, ht⟩]
        rfl
      · change stateVertex w (k.succ,q) = _
        rw [hk]

lemma graph_reach_state (finish : Q) (w : List Alpha) (c c' : Machine.Config (Q := Q) w) :
    (graph M finish w).Reach (stateVertex w c) (stateVertex w c') ↔
      Relation.ReflTransGen (M.Step w) c c' := by
  constructor
  · intro h
    have aux (v : Vertex Q w.length) (hv : (graph M finish w).Reach (stateVertex w c) v) :
        ∃ d, v = stateVertex w d ∧ Relation.ReflTransGen (M.Step w) c d := by
      induction hv with
      | refl => exact ⟨c,rfl,.refl⟩
      | @tail v v' _ hvv ih =>
        obtain ⟨d,rfl,hd⟩ := ih
        obtain ⟨d',he,hs⟩ := (graph_step_from_state M finish w d v').mp hvv
        exact ⟨d',he,hd.tail hs⟩
    obtain ⟨d,hd,hp⟩ := aux _ h
    exact stateVertex_injective w hd ▸ hp
  · intro h
    exact h.lift (stateVertex w) (fun a b hab =>
      (graph_step_from_state M finish w a _).mpr ⟨b,rfl,hab⟩)

lemma graph_terminal (finish : Q) (w : List Alpha) (t : Machine.Config (Q := Q) w)
    (ht : M.transition t.2 (scanned w t.1) = none) :
    ∀ e, (graph M finish w).src e ≠ stateVertex w t := by
  intro e he
  obtain ⟨c,_,d,hd,_⟩ := (graph_step_from_state M finish w t _).mp ⟨e,he,rfl⟩
  simp [ht] at hd

lemma scanned_outCell (w : List Alpha) (s : Bool) :
    scanned w (outCell w.length s) = if s then .right else .left := by
  cases s with
  | false => exact (scanned_eq_left_iff _ _).mpr rfl
  | true => exact (scanned_eq_right_iff _ _).mpr rfl

lemma test_destination (finish : Q) (w : List Alpha) (s : Bool) :
    (graph M finish w).dst (.inr (.inr (s,testSlot M finish))) =
      stateVertex w (outCell w.length s,if s then finish else M.initial) := by
  classical
  change Sum.inl (_,localVertex M finish _ _) = _
  rw [scanned_outCell]
  cases s <;> simp [localVertex, outward, stateVertex]

lemma test_step (finish : Q) (w : List Alpha) (s : Bool) :
    (graph M finish w).Step (.inr (s,testSlot M finish))
      (stateVertex w (outCell w.length s,if s then finish else M.initial)) :=
  ⟨.inr (.inr (s,testSlot M finish)),rfl,test_destination M finish w s⟩

end CellNetwork
end Complexity.FiniteAutomaton
