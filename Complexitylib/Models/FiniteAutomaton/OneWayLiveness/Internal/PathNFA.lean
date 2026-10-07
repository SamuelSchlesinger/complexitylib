/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Models.FiniteAutomaton.OneWayLiveness.Internal.Normalization

/-!
# One-way-liveness proof: PathNFA

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Automata/PathNFA.lean

Module and namespace names, imports, and formatting are adapted to complexitylib.
The machine definitions are shared through `Models.FiniteAutomaton.Defs`.
-/

@[expose] public section

namespace Complexity.FiniteAutomaton

/-- A nondeterministic automaton on an arbitrary state type. -/
structure NMachineOn (Alpha Q : Type) where
  /-- The initial control state. -/
  initial : Q
  /-- The accepting control states. -/
  accepting : Set Q
  /-- The next control states and head moves for each scanned symbol. -/
  transition : Q → Symbol Alpha → Set (Q × Move)
  left_boundary : ∀ q q', (q', .left) ∉ transition q .left
  right_boundary : ∀ q q', (q', .right) ∉ transition q .right

namespace NMachineOn
variable {Alpha Q : Type} (M : NMachineOn Alpha Q)
/-- A position on the endmarked word and a nondeterministic control state. -/
abbrev Config (w : List Alpha) := Fin (w.length+2) × Q

/-- One nondeterministic transition on the scanned input symbol. -/
def Step (w : List Alpha) (c c' : Config (Q := Q) w) : Prop :=
  ∃ d, (c'.2,d) ∈ M.transition c.2 (scanned w c.1) ∧ d.Rel c.1.val c'.1.val

/-- Existence of a finite run reaching an accepting control state. -/
def Accepts (positive : Bool) (w : List Alpha) : Prop :=
  ∃ c, FiniteRun positive (M.Step w) (⟨0,by omega⟩,M.initial) c ∧ c.2 ∈ M.accepting

/-- Number the states using an equivalence, preserving transitions and endmarkers. -/
def relabel {n : ℕ} (e : Q ≃ Fin n) : NMachine Alpha n where
  initial := e M.initial
  accepting := {q | e.symm q ∈ M.accepting}
  transition q b := {p | (e.symm p.1,p.2) ∈ M.transition (e.symm q) b}
  left_boundary q q' := M.left_boundary (e.symm q) (e.symm q')
  right_boundary q q' := M.right_boundary (e.symm q) (e.symm q')

lemma relabel_accepts {n : ℕ} (e : Q ≃ Fin n) (positive : Bool) (w : List Alpha) :
    (M.relabel e).Accepts positive w ↔ M.Accepts positive w := by
  have hfor {c c' : Fin (w.length+2) × Fin n} (hs : (M.relabel e).Step w c c') :
      M.Step w (c.1,e.symm c.2) (c'.1,e.symm c'.2) := hs
  have hback {c c' : Config (Q := Q) w} (hs : M.Step w c c') :
      (M.relabel e).Step w (c.1,e c.2) (c'.1,e c'.2) := by
    simpa only [NMachine.Step, Step, relabel, Set.mem_ofPred_eq, Equiv.symm_apply_apply] using hs
  unfold NMachine.Accepts Accepts
  constructor
  · rintro ⟨c,hc,ha⟩
    refine ⟨(c.1,e.symm c.2),?_,ha⟩
    cases positive <;> simp only [FiniteRun, Bool.false_eq_true, ↓reduceIte] at hc ⊢
    · simpa only [Function.onFun, relabel, Equiv.symm_apply_apply] using
        hc.lift (fun c => (c.1,e.symm c.2)) (fun _ _ h => hfor h)
    · simpa only [Function.onFun, relabel, Equiv.symm_apply_apply] using
        hc.lift (fun c => (c.1,e.symm c.2)) (fun _ _ h => hfor h)
  · rintro ⟨c,hc,ha⟩
    refine ⟨(c.1,e c.2),?_,
      by simpa only [relabel, Set.mem_ofPred_eq, Equiv.symm_apply_apply] using ha⟩
    cases positive <;> simp only [FiniteRun, Bool.false_eq_true, ↓reduceIte] at hc ⊢
    · exact hc.lift (fun c => (c.1,e c.2)) (fun _ _ h => hback h)
    · exact hc.lift (fun c => (c.1,e c.2)) (fun _ _ h => hback h)

lemma relabel_noLeft {n : ℕ} (e : Q ≃ Fin n)
    (hm : ∀ q b q', (q',.left) ∉ M.transition q b) : (M.relabel e).NoLeft :=
  fun q b q' => hm (e.symm q) b (e.symm q')
end NMachineOn

namespace PathNFA
variable {H : Type}
/-- `none` is the initial state. Boolean states are accept and reject. -/
abbrev State (H : Type) := Option (H ⊕ Bool)
/-- A path state recording the current relation-product endpoint. -/
abbrev path (p : H) : State H := some (.inl p)
/-- The distinguished accepting state of the relation-product automaton. -/
abbrev accept : State H := some (.inr false)

/-- Choose a start vertex, follow relation edges, and accept at the right endmarker. -/
def rules : State H → Symbol (BRel H) → Set (State H × Move)
  | none, .left => {c | ∃ p, c = (path p,.right)}
  | some (.inl p), .letter R => {c | ∃ q, c = (path q,.right) ∧ R.holds p q}
  | some (.inl _), .right => {(accept,.stay)}
  | _, _ => ∅

lemma rules_noLeft (q : State H) (b : Symbol (BRel H)) (q' : State H) :
    (q',.left) ∉ rules q b := by
  cases q with
  | none => cases b <;> simp [rules]
  | some q => cases q with
    | inl p => cases b <;> simp [rules]
    | inr b' => cases b <;> simp [rules]

/-- The one-way endmarker automaton for nonempty relation products. -/
def machine : NMachineOn (BRel H) (State H) where
  initial := none
  accepting := {accept}
  transition := rules
  left_boundary q q' := rules_noLeft q .left q'
  right_boundary q q' := by
    cases q with
    | none => simp [rules]
    | some q => cases q <;> simp [rules]

/-- A numbered path through a product, extended arbitrarily after its endpoint. -/
lemma product_path (w : List (BRel H)) (a b : H) :
    w.prod.holds a b ↔ ∃ p : ℕ → H, p 0 = a ∧ p w.length = b ∧
      ∀ i (hi : i < w.length), w[i].holds (p i) (p (i+1)) := by
  induction w generalizing a with
  | nil =>
    simp only [List.prod_nil, BRel.one_holds, List.length_nil, Nat.not_lt_zero, IsEmpty.forall_iff,
      implies_true, and_true]
    constructor
    · intro h; exact ⟨fun _ => a,rfl,h⟩
    · rintro ⟨p,hp,hq⟩; exact hp.symm.trans hq
  | cons R w ih =>
    simp only [List.prod_cons, BRel.mul_holds]
    constructor
    · rintro ⟨c,hR,hc⟩
      obtain ⟨p,hp,hb,hs⟩ := (ih c).mp hc
      let q : ℕ → H := fun i => match i with | 0 => a | i+1 => p i
      refine ⟨q,rfl,hb,?_⟩
      intro i hi
      cases i with
      | zero => simpa only [q, List.getElem_cons_zero, hp] using hR
      | succ i => exact hs i (by simpa using hi)
    · rintro ⟨p,hp,hb,hs⟩
      refine ⟨p 1,?_,(ih (p 1)).mpr ⟨fun i => p (i+1),rfl,hb,?_⟩⟩
      · rw [← hp]; exact hs 0 (by simp)
      · intro i hi
        exact hs (i+1) (by simpa using hi)

/-- The accumulated product on every prefix reached by a path state. -/
def Good (w : List (BRel H)) (c : NMachineOn.Config (Q := State H) w) : Prop :=
  match c.2 with
  | none => c.1.val = 0
  | some (.inl p) => 1 ≤ c.1.val ∧ ∃ a, (w.take (c.1.val-1)).prod.holds a p
  | some (.inr false) => BRel.Live w
  | some (.inr true) => False

lemma scanned_letter_data (w : List (BRel H)) (i : Fin (w.length+2)) (R : BRel H)
    (hs : scanned w i = .letter R) : ∃ hi : i.val-1 < w.length, w[i.val-1] = R := by
  unfold scanned at hs
  split_ifs at hs with h0 hi
  exact ⟨by omega, Symbol.letter.inj hs⟩

lemma scanned_letter_cell (w : List (BRel H)) (i : ℕ) (hi : i < w.length) :
    scanned w ⟨i+1,by omega⟩ = .letter w[i] := by
  simp [scanned, show i+1 < w.length+1 by omega]

lemma good_step (w : List (BRel H)) (c c' : NMachineOn.Config (Q := State H) w)
    (hg : Good w c) (hs : machine.Step w c c') : Good w c' := by
  rcases c with ⟨i,q⟩
  rcases c' with ⟨j,r⟩
  rcases hs with ⟨d,hd,hm⟩
  change (r,d) ∈ rules q (scanned w i) at hd
  cases q with
  | none =>
    change i.val = 0 at hg
    cases hb : scanned w i with
    | left =>
      rw [hb] at hd
      obtain ⟨p,he⟩ := hd
      have hr := congrArg Prod.fst he
      have hdir := congrArg Prod.snd he
      dsimp only at hr hdir
      subst r d
      change j.val = i.val+1 at hm
      change 1 ≤ j.val ∧ ∃ a, (w.take (j.val-1)).prod.holds a p
      refine ⟨by omega,p,?_⟩
      simp [show j.val-1 = 0 by omega]
    | letter R => simp [hb,rules] at hd
    | right => simp [hb,rules] at hd
  | some q =>
    cases q with
    | inl p =>
      obtain ⟨hip,a,ha⟩ := hg
      change 1 ≤ i.val at hip
      change (w.take (i.val-1)).prod.holds a p at ha
      cases hb : scanned w i with
      | left => simp [hb,rules] at hd
      | letter R =>
        rw [hb] at hd
        obtain ⟨q,he,hR⟩ := hd
        have hr := congrArg Prod.fst he
        have hdir := congrArg Prod.snd he
        dsimp only at hr hdir
        subst r d
        change j.val = i.val+1 at hm
        obtain ⟨hi,hRi⟩ := scanned_letter_data w i R hb
        change 1 ≤ j.val ∧ ∃ a, (w.take (j.val-1)).prod.holds a q
        refine ⟨by omega,a,?_⟩
        rw [show j.val-1 = (i.val-1)+1 by omega, List.take_succ_eq_append_getElem hi]
        simp only [List.prod_append, List.prod_cons, List.prod_nil, mul_one, BRel.mul_holds]
        exact ⟨p,ha,hRi ▸ hR⟩
      | right =>
        rw [hb] at hd
        have he : (r,d) = (accept,.stay) := hd
        have hr := congrArg Prod.fst he
        dsimp only at hr
        subst r
        change BRel.Live w
        have hi := (scanned_eq_right_iff w i).mp hb
        exact ⟨a,p,by simpa only [hi,Nat.add_sub_cancel,List.take_length] using ha⟩
    | inr b => cases hb : scanned w i <;> simp [rules] at hd

lemma accepts_iff (positive : Bool) (w : List (BRel H)) :
    machine.Accepts positive w ↔ BRel.Live w := by
  constructor
  · rintro ⟨c,hc,ha⟩
    have hr : Relation.ReflTransGen (machine.Step w) (⟨0,by omega⟩,none) c := by
      cases positive with
      | false => exact hc
      | true => exact hc.to_reflTransGen
    have hg : Good w c := by
      clear hc ha
      induction hr with
      | refl => rfl
      | @tail c d hcd hstep ih => exact good_step w c d ih hstep
    have hac : c.2 = accept := ha
    simpa only [Good,hac] using hg
  · rintro ⟨a,b,hprod⟩
    obtain ⟨p,_hp,_hb,hpath⟩ := (product_path w a b).mp hprod
    let cell (i : ℕ) (hi : i ≤ w.length) : NMachineOn.Config (Q := State H) w :=
      (⟨i+1,by omega⟩,path (p i))
    have reach (i : ℕ) (hi : i ≤ w.length) :
        Relation.ReflTransGen (machine.Step w) (cell 0 (by omega)) (cell i hi) := by
      induction i with
      | zero => exact .refl
      | succ i ih =>
        refine (ih (by omega)).tail ?_
        refine ⟨.right,?_,rfl⟩
        change (path (p (i+1)),.right) ∈ rules (path (p i)) (scanned w ⟨i+1,by omega⟩)
        rw [scanned_letter_cell w i (by omega)]
        exact ⟨p (i+1),rfl,hpath i (by omega)⟩
    have first : machine.Step w (⟨0,by omega⟩,none) (cell 0 (by omega)) := by
      refine ⟨.right,?_,rfl⟩
      change (path (p 0),.right) ∈ rules none (scanned w 0)
      simp only [scanned, Fin.val_zero, ↓reduceDIte]
      exact ⟨p 0,rfl⟩
    let last : NMachineOn.Config (Q := State H) w := (⟨w.length+1,by omega⟩,accept)
    have final : machine.Step w (cell w.length le_rfl) last := by
      refine ⟨.stay,?_,rfl⟩
      change (accept,.stay) ∈ rules (path (p w.length)) (scanned w ⟨w.length+1,by omega⟩)
      rw [(scanned_eq_right_iff _ _).mpr rfl]
      exact Set.mem_singleton _
    have hp : Relation.TransGen (machine.Step w) (⟨0,by omega⟩,none) last :=
      (Relation.TransGen.head' first (reach w.length le_rfl)).tail final
    refine ⟨last,?_,rfl⟩
    cases positive with
    | false => exact hp.to_reflTransGen
    | true => exact hp

end PathNFA

/-- The explicit path automaton has h+3 states, including the unused rejector.
It accepts only after at least two transitions, so both conventions agree. -/
theorem small_nfa (h : ℕ) :
    ∃ N : NMachine (Alphabet h) (h+3), N.NoLeft ∧
      ∀ positive : Bool, N.Recognizes positive (oneWayLiveness h) := by
  classical
  let e : PathNFA.State (Fin h) ≃ Fin (h+3) := Fintype.equivFinOfCardEq (by
    simp only [PathNFA.State, Fintype.card_option, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_bool])
  refine ⟨PathNFA.machine.relabel e, PathNFA.machine.relabel_noLeft e PathNFA.rules_noLeft, ?_⟩
  intro positive w
  exact (PathNFA.machine.relabel_accepts e positive w).trans (PathNFA.accepts_iff positive w)

end Complexity.FiniteAutomaton
