/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Models.FiniteAutomaton.OneWayLiveness.Internal.Model

/-!
# One-way-liveness proof: Normalization

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Automata/Normalization.lean

Module and namespace names, imports, and formatting are adapted to complexitylib.
The machine definitions are shared through `Models.FiniteAutomaton.Defs`.
-/

@[expose] public section

namespace Complexity.FiniteAutomaton

/-- A deterministic automaton on an arbitrary state type. -/
structure Machine (Alpha Q : Type) where
  /-- The initial control state. -/
  initial : Q
  /-- The accepting control states. -/
  accepting : Set Q
  /-- The next control states and head moves for each scanned symbol. -/
  transition : Q → Symbol Alpha → Option (Q × Move)
  left_boundary : ∀ q q', transition q .left ≠ some (q', .left)
  right_boundary : ∀ q q', transition q .right ≠ some (q', .right)

namespace Machine
variable {Alpha Q : Type}
variable (M : Machine Alpha Q)
/-- A position on the endmarked word and a control state. -/
abbrev Config (w : List Alpha) := Fin (w.length + 2) × Q

/-- One deterministic transition on the scanned input symbol. -/
def Step (w : List Alpha) (c c' : Config (Q := Q) w) : Prop :=
  ∃ d, M.transition c.2 (scanned w c.1) = some (c'.2, d) ∧ d.Rel c.1.val c'.1.val

/-- A finite run from the initial configuration reaches an accepting state. -/
def Accepts (positive : Bool) (w : List Alpha) : Prop :=
  ∃ c, FiniteRun positive (M.Step w) (⟨0, by omega⟩, M.initial) c ∧ c.2 ∈ M.accepting

end Machine

/-- View a numbered-state deterministic automaton as an arbitrary-state machine. -/
def DMachine.toMachine {Alpha : Type} {s : ℕ} (M : DMachine Alpha s) : Machine Alpha (Fin s) :=
  ⟨M.initial, M.accepting, M.transition, M.left_boundary, M.right_boundary⟩

lemma DMachine.toMachine_accepts {Alpha : Type} {s : ℕ} (M : DMachine Alpha s)
    (positive : Bool) (w : List Alpha) :
    M.toMachine.Accepts positive w ↔ M.Accepts positive w := Iff.rfl

namespace Machine
variable {Alpha Q : Type} (M : Machine Alpha Q)

/-- A fresh nonaccepting initial state copies the original initial row. -/
def positiveCopy : Machine Alpha (Option Q) where
  initial := none
  accepting := {q | ∃ a, q = some a ∧ a ∈ M.accepting}
  transition q b := (M.transition (q.getD M.initial) b).map (fun x => (some x.1, x.2))
  left_boundary q q' h := by
    cases ht : M.transition (q.getD M.initial) .left with
    | none => simp [ht] at h
    | some x =>
      rcases x with ⟨r, d⟩
      simp only [ht, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      exact M.left_boundary _ r (h.2 ▸ ht)
  right_boundary q q' h := by
    cases ht : M.transition (q.getD M.initial) .right with
    | none => simp [ht] at h
    | some x =>
      rcases x with ⟨r, d⟩
      simp only [ht, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      exact M.right_boundary _ r (h.2 ▸ ht)

lemma positiveCopy_step (w : List Alpha) (i : Fin (w.length + 2)) (q : Option Q)
    (c' : Config (Q := Option Q) w) :
    M.positiveCopy.Step w (i, q) c' ↔
      ∃ r, c'.2 = some r ∧ M.Step w (i, q.getD M.initial) (c'.1, r) := by
  constructor
  · rintro ⟨d, hd, hr⟩
    change (M.transition _ _).map _ = some _ at hd
    obtain ⟨⟨r, e⟩, ht, he⟩ := Option.map_eq_some_iff.mp hd
    simp only [Prod.mk.injEq] at he
    exact ⟨r, he.1.symm, e, ht, he.2 ▸ hr⟩
  · rintro ⟨r, hr, d, ht, hd⟩
    refine ⟨d, ?_, hd⟩
    change (M.transition _ _).map _ = some _
    simp only [ht, Option.map_some, hr]

lemma positiveCopy_reach (w : List Alpha) (c c' : Config (Q := Q) w) :
    Relation.ReflTransGen (M.positiveCopy.Step w) (c.1, some c.2) (c'.1, some c'.2) ↔
      Relation.ReflTransGen (M.Step w) c c' := by
  have forward (a b : Config (Q := Option Q) w)
      (h : Relation.ReflTransGen (M.positiveCopy.Step w) a b) :
      ∀ q, a.2 = some q → ∃ r, b.2 = some r ∧
      Relation.ReflTransGen (M.Step w) (a.1, q) (b.1, r) := by
    induction h with
    | refl => exact fun q hq => ⟨q, hq, .refl⟩
    | @tail b d hab hbd ih =>
      intro q hq
      obtain ⟨r, hr, hpath⟩ := ih q hq
      obtain ⟨r', hr', hd⟩ := (M.positiveCopy_step w b.1 b.2 d).mp hbd
      exact ⟨r', hr', hpath.tail (by simpa only [hr, Option.getD_some] using hd)⟩
  constructor
  · intro h
    obtain ⟨r, hr, hp⟩ := forward _ _ h c.2 rfl
    cases Option.some.inj hr
    exact hp
  · intro h
    exact h.lift (fun a => (a.1, some a.2)) (fun a b hab =>
      (M.positiveCopy_step w a.1 (some a.2) _).mpr ⟨b.2, rfl, hab⟩)

lemma positiveCopy_accepts (w : List Alpha) :
    M.positiveCopy.Accepts false w ↔ M.Accepts true w := by
  simp only [Accepts, FiniteRun, Bool.false_eq_true, ↓reduceIte]
  constructor
  · rintro ⟨c, hpath, q, hq, hacc⟩
    rcases hpath.cases_head with he | ⟨v, hv, hvc⟩
    · have : c.2 = none := congrArg Prod.snd he.symm
      simp [this] at hq
    · obtain ⟨r, hr, hs⟩ := (M.positiveCopy_step w _ none v).mp hv
      have hvq : Relation.ReflTransGen (M.Step w) (v.1, r) (c.1, q) := by
        apply (M.positiveCopy_reach w (v.1, r) (c.1, q)).mp
        have hv : v = (v.1, some r) := Prod.ext rfl hr
        have hc : c = (c.1, some q) := Prod.ext rfl hq
        rwa [hv, hc] at hvc
      exact ⟨(c.1, q), Relation.TransGen.head' hs hvq, hacc⟩
  · rintro ⟨c, hpath, hacc⟩
    obtain ⟨v, hs, hvc⟩ := Relation.TransGen.head'_iff.mp hpath
    refine ⟨(c.1, some c.2), ?_, c.2, rfl, hacc⟩
    exact ((M.positiveCopy_reach w v c).mpr hvc).head
      ((M.positiveCopy_step w _ none (v.1, some v.2)).mpr ⟨v.2, rfl, hs⟩)


/-- Sink normalization also replaces missing transitions at accepting states. -/
noncomputable def sinkCopy : Machine Alpha (Option Q) := by
  classical
  exact {
    initial := some M.initial
    accepting := {none}
    transition := fun q b => match q with
      | some q => if q ∈ M.accepting then some (none, .stay)
          else (M.transition q b).map (fun x => (some x.1, x.2))
      | none => match b with
        | .right => none
        | _ => some (none, .right)
    left_boundary := by
      intro q q' h
      cases q with
      | none => simp at h
      | some q =>
        dsimp only at h
        split_ifs at h with hq
        · cases h
        · obtain ⟨⟨r,d⟩, ht, he⟩ := Option.map_eq_some_iff.mp h
          simp only [Prod.mk.injEq] at he
          exact M.left_boundary _ r (he.2 ▸ ht)
    right_boundary := by
      intro q q' h
      cases q with
      | none => cases h
      | some q =>
        dsimp only at h
        split_ifs at h with hq
        · cases h
        · obtain ⟨⟨r,d⟩, ht, he⟩ := Option.map_eq_some_iff.mp h
          simp only [Prod.mk.injEq] at he
          exact M.right_boundary _ r (he.2 ▸ ht) }

lemma sinkCopy_step_old (w : List Alpha) (c : Config (Q := Q) w)
    (c' : Config (Q := Option Q) w) :
    M.sinkCopy.Step w (c.1, some c.2) c' ↔
      (c.2 ∈ M.accepting ∧ c' = (c.1, none)) ∨
      (c.2 ∉ M.accepting ∧ ∃ r, c'.2 = some r ∧ M.Step w c (c'.1, r)) := by
  classical
  simp only [Step, sinkCopy]
  by_cases ha : c.2 ∈ M.accepting
  · simp only [ha, ↓reduceIte, Option.some.injEq, Prod.mk.injEq, true_and, not_true_eq_false,
      false_and, or_false]
    constructor
    · rintro ⟨d, ⟨hq, rfl⟩, hd⟩
      exact Prod.ext (Fin.ext hd) hq.symm
    · rintro rfl
      exact ⟨.stay, ⟨rfl, rfl⟩, rfl⟩
  · simp only [ha, ↓reduceIte, false_and, not_false_eq_true, true_and, false_or]
    constructor
    · rintro ⟨d, hd, hr⟩
      obtain ⟨⟨r,e⟩, ht, he⟩ := Option.map_eq_some_iff.mp hd
      simp only [Prod.mk.injEq] at he
      exact ⟨r, he.1.symm, e, ht, he.2 ▸ hr⟩
    · rintro ⟨r, hr, d, ht, hd⟩
      exact ⟨d, by simp only [ht, Option.map_some, hr], hd⟩

end Machine

lemma scanned_eq_left_iff {Alpha : Type} (w : List Alpha) (i : Fin (w.length + 2)) :
    scanned w i = .left ↔ i.val = 0 := by
  simp only [scanned]
  split_ifs <;> simp_all

lemma scanned_eq_right_iff {Alpha : Type} (w : List Alpha) (i : Fin (w.length + 2)) :
    scanned w i = .right ↔ i.val = w.length + 1 := by
  simp only [scanned]
  split_ifs <;> simp_all <;> omega

namespace Machine
variable {Alpha Q : Type} (M : Machine Alpha Q)

/-- The fresh sink state at the right endmarker. -/
def terminal (w : List Alpha) : Config (Q := Option Q) w := (⟨w.length + 1, by omega⟩, none)

lemma sinkCopy_sweep (w : List Alpha) (i : Fin (w.length + 2)) :
    Relation.ReflTransGen (M.sinkCopy.Step w) (i, none) (terminal w) := by
  classical
  induction i using Fin.reverseInduction with
  | last => exact .refl
  | @cast i ih =>
    apply ih.head
    refine ⟨.right, ?_, rfl⟩
    change (match scanned w i.castSucc with | .right => none | _ => some (none, Move.right)) = _
    have hn : scanned w i.castSucc ≠ .right := by
      rw [ne_eq, scanned_eq_right_iff]
      exact Nat.ne_of_lt i.isLt
    cases h : scanned w i.castSucc <;> simp_all

lemma sinkCopy_reach_iff (w : List Alpha) (c : Config (Q := Q) w) :
    Relation.ReflTransGen (M.sinkCopy.Step w) (c.1, some c.2) (terminal w) ↔
      ∃ a, Relation.ReflTransGen (M.Step w) c a ∧ a.2 ∈ M.accepting := by
  classical
  constructor
  · intro hp
    have aux (b : Config (Q := Option Q) w)
        (h : Relation.ReflTransGen (M.sinkCopy.Step w) b (terminal w)) :
        ∀ q, b.2 = some q →
          ∃ a, Relation.ReflTransGen (M.Step w) (b.1,q) a ∧ a.2 ∈ M.accepting := by
      induction h using Relation.ReflTransGen.head_induction_on with
      | refl => intro q hq; cases hq
      | @head b d hbd _ ih =>
        intro q hq
        have hb : b = (b.1, some q) := Prod.ext rfl hq
        rw [hb] at hbd
        rcases (M.sinkCopy_step_old w (b.1,q) d).mp hbd with ⟨ha, _⟩ | ⟨_hn, r, hr, hs⟩
        · exact ⟨(b.1,q), .refl, ha⟩
        · obtain ⟨a, hda, ha⟩ := ih r hr
          exact ⟨a, hda.head hs, ha⟩
    exact aux _ hp c.2 rfl
  · rintro ⟨a, hp, ha⟩
    induction hp using Relation.ReflTransGen.head_induction_on with
    | refl =>
      exact (M.sinkCopy_sweep w a.1).head
        ((M.sinkCopy_step_old w a (a.1,none)).mpr (.inl ⟨ha, rfl⟩))
    | @head b d hbd _ ih =>
      by_cases hb : b.2 ∈ M.accepting
      · exact (M.sinkCopy_sweep w b.1).head
          ((M.sinkCopy_step_old w b (b.1,none)).mpr (.inl ⟨hb, rfl⟩))
      · exact ih.head ((M.sinkCopy_step_old w b (d.1,some d.2)).mpr (.inr ⟨hb, d.2, rfl, hbd⟩))

lemma sinkCopy_accepts (w : List Alpha) :
    Relation.ReflTransGen (M.sinkCopy.Step w) (⟨0, by omega⟩, some M.initial) (terminal w) ↔
      M.Accepts false w := M.sinkCopy_reach_iff w (⟨0, by omega⟩, M.initial)

lemma sinkCopy_terminal (w : List Alpha) :
    M.sinkCopy.transition (terminal (Q := Q) w).2 (scanned w (terminal (Q := Q) w).1) = none := by
  have hs : scanned w (terminal (Q := Q) w).1 = .right := (scanned_eq_right_iff _ _).mpr rfl
  classical
  change (match scanned w (terminal (Q := Q) w).1 with
    | .right => none | _ => some (none, Move.right)) = none
  rw [hs]

end Machine
end Complexity.FiniteAutomaton
