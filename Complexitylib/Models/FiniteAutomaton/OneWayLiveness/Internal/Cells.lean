/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Models.FiniteAutomaton.OneWayLiveness.Internal.Wiring

/-!
# One-way-liveness proof: Cells

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Automata/Cells.lean

Module and namespace names, imports, and formatting are adapted to complexitylib.
The machine definitions are shared through `Models.FiniteAutomaton.Defs`.
-/

@[expose] public section

namespace Complexity.FiniteAutomaton
namespace Pairing
variable {P I : Type} [Fintype P] [Fintype I]

lemma transport_compatible {P Q C : Type*} (a : Pairing P) (e : P ≃ Q) (c : Q → C) :
    (a.transport e).Compatible c ↔ a.Compatible (c ∘ e) := by
  constructor
  · intro h x y hxy
    exact h (e x) (e y) (by simpa only [transport, Equiv.symm_apply_apply] using hxy)
  · intro h x y hxy
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using h _ _ hxy

/-- Close all internal tips with a matching of local joins. -/
noncomputable def close (lanes : Pairing (P ⊕ I)) (joins : Pairing I) : Pairing P :=
  (compose lanes (joins.transport (Equiv.sumEmpty I Empty).symm)).transport (Equiv.sumEmpty P Empty)

lemma close_compatible (lanes : Pairing (P ⊕ I)) (joins : Pairing I) (c : P → Bool) :
    (close lanes joins).Compatible c ↔
    ∃ f : I → Bool, lanes.Compatible (Sum.elim c f) ∧ joins.Compatible f := by
  rw [close, transport_compatible]
  have hc : c ∘ (Equiv.sumEmpty P Empty) = Sum.elim c (fun e => e.elim) := by
    funext p; cases p with | inl p => rfl | inr p => exact p.elim
  rw [hc, compose_compatible]
  apply exists_congr
  intro f
  rw [transport_compatible]
  rfl

lemma ofInvolution_compatible {P C : Type*} (f : P → P) (hf : Function.Involutive f)
    (hn : ∀ p, f p ≠ p) (c : P → C) :
    (ofInvolution f hf hn).Compatible c ↔ ∀ p, c p = c (f p) := by
  constructor
  · intro h p; exact h p (f p) rfl
  · intro h p q hpq; cases hpq; exact h p

end Pairing

namespace CellNetwork
variable (Q : Type)
/-- `true` directs the prospective successor to the right. -/
abbrev Slot := Bool × Q × Q
/-- A directed transition slot together with one of its two lanes. -/
abbrev Port := Slot Q × Bool
/-- A transition slot labelled by the side of the cell. -/
abbrev Boundary := Bool × Slot Q
/-- Boundary incidences and the two ends of stationary-transition edges. -/
abbrev Incidence := Boundary Q ⊕ ((Q × Q) × Bool)
/-- An incidence together with its lane. -/
abbrev Tip := Incidence Q × Bool
/-- Machine states and unattached incidences within a cell. -/
abbrev LocalVertex := Q ⊕ Incidence Q

/-- A lane's absolute label changes its incoming/outgoing role between
opposite sides of a cell. -/
def tipRole (side lane : Bool) : Bool := side ^^ lane
@[simp] lemma tipRole_twice (s l : Bool) : tipRole s (tipRole s l) = l := by
  cases s <;> cases l <;> rfl
@[simp] lemma tipRole_ne (s l : Bool) : tipRole (!s) l = !(tipRole s l) := by
  cases s <;> cases l <;> rfl

/-- All stay candidates are allowed locally; a nontransition candidate will
be attached to a fresh leaf. This leaves the external degree unchanged. -/
def laneMate : ((Boundary Q × Bool) ⊕ Tip Q) → ((Boundary Q × Bool) ⊕ Tip Q)
  | .inl (b,l) => .inr (.inl b, tipRole b.1 l)
  | .inr (.inl b,t) => .inl (b, tipRole b.1 t)
  | .inr (.inr (pq,r),t) => .inr (.inr (pq,!r),!t)

lemma laneMate_involutive : Function.Involutive (laneMate Q) := by
  rintro (⟨⟨s,slot⟩,l⟩ | ⟨(⟨s,slot⟩ | ⟨pq,r⟩),t⟩) <;> simp [laneMate]
lemma laneMate_ne (p) : laneMate Q p ≠ p := by
  rcases p with ⟨⟨s,slot⟩,l⟩ | ⟨(⟨s,slot⟩ | ⟨pq,r⟩),t⟩ <;> simp [laneMate]

/-- The pairing connecting boundary lanes and stationary-transition tips. -/
def lanes : Pairing ((Boundary Q × Bool) ⊕ Tip Q) :=
  Pairing.ofInvolution (laneMate Q) (laneMate_involutive Q) (laneMate_ne Q)

/-- Join a forward tip to its successor and a backward tip to its predecessor. -/
def joinMate (r : Equiv.Perm (Incidence Q)) : Tip Q → Tip Q
  | (i,false) => (r i, true)
  | (i,true) => (r.symm i, false)

lemma joinMate_involutive (r : Equiv.Perm (Incidence Q)) : Function.Involutive (joinMate Q r) := by
  rintro ⟨i, b⟩; cases b <;> simp [joinMate]
lemma joinMate_ne (r : Equiv.Perm (Incidence Q)) (p) : joinMate Q r p ≠ p := by
  rcases p with ⟨i,b⟩; cases b <;> simp [joinMate]

/-- The tip pairing induced by the cyclic incidence order. -/
def joins (r : Equiv.Perm (Incidence Q)) : Pairing (Tip Q) :=
  Pairing.ofInvolution (joinMate Q r) (joinMate_involutive Q r) (joinMate_ne Q r)

lemma lanes_compatible (c : Boundary Q × Bool → Bool) (f : Tip Q → Bool) :
    (lanes Q).Compatible (Sum.elim c f) ↔
    (∀ b l, c (b,l) = f (.inl b, tipRole b.1 l)) ∧
    (∀ pq r t, f (.inr (pq,r),t) = f (.inr (pq,!r),!t)) := by
  rw [lanes, Pairing.ofInvolution_compatible]
  constructor
  · intro h; exact ⟨fun b l => h (.inl (b,l)), fun pq r t => h (.inr (.inr (pq,r),t))⟩
  · rintro ⟨hb, hs⟩ (⟨b,l⟩ | ⟨(b | ⟨pq,r⟩),t⟩)
    · exact hb b l
    · simpa only [laneMate, Sum.elim_inl, Sum.elim_inr, tipRole_twice] using
        (hb b (tipRole b.1 t)).symm
    · exact hs pq r t

lemma joins_compatible (r : Equiv.Perm (Incidence Q)) (f : Tip Q → Bool) :
    (joins Q r).Compatible f ↔ ∀ i, f (i,false) = f (r i,true) := by
  rw [joins, Pairing.ofInvolution_compatible]
  constructor
  · exact fun h i => h (i,false)
  · intro h ⟨i,b⟩
    cases b with
    | false => exact h i
    | true => simpa [joinMate] using (h (r.symm i)).symm

/-- The two sides use exactly the same slot/lane labels. -/
def portsEquiv : (Boundary Q × Bool) ≃ (Port Q ⊕ Port Q) where
  toFun p := if p.1.1 then .inr (p.1.2,p.2) else .inl (p.1.2,p.2)
  invFun p := p.elim (fun p => ((false,p.1),p.2)) (fun p => ((true,p.1),p.2))
  left_inv p := by rcases p with ⟨⟨s,slot⟩,l⟩; cases s <;> rfl
  right_inv p := by cases p <;> rfl

/-- Close the internal tips to obtain the cell boundary pairing. -/
noncomputable def diagram [Fintype Q] (r : Equiv.Perm (Incidence Q)) : Pairing (Port Q ⊕ Port Q) :=
  (Pairing.close (lanes Q) (joins Q r)).transport (portsEquiv Q)

lemma diagram_compatible [Fintype Q] (r : Equiv.Perm (Incidence Q))
    (left right : Port Q → Bool) :
    (diagram Q r).Compatible (Sum.elim left right) ↔ ∃ f : Tip Q → Bool,
    (∀ s slot l, (if s then right else left) (slot,l) = f (.inl (s,slot),tipRole s l)) ∧
    (∀ pq role t, f (.inr (pq,role),t) = f (.inr (pq,!role),!t)) ∧
    (∀ i, f (i,false) = f (r i,true)) := by
  rw [diagram, Pairing.transport_compatible, Pairing.close_compatible]
  apply exists_congr
  intro f
  rw [lanes_compatible, joins_compatible, and_assoc]
  apply and_congr_left
  intro _
  constructor
  · intro h s slot l
    cases s with
    | false => simpa [portsEquiv] using h (false,slot) l
    | true => simpa [portsEquiv] using h (true,slot) l
  · intro h ⟨s,slot⟩ l
    cases s with
    | false => simpa [portsEquiv] using h false slot l
    | true => simpa [portsEquiv] using h true slot l

end CellNetwork
end Complexity.FiniteAutomaton
